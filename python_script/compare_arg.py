import os
import sys
import subprocess
import re

from collections import defaultdict


class Compare():
    # compare the recovered function signature for obfuscated and non-obfuscated binaries
    def __init__(self):
        self.type_armor_path = "/home/yanlin/toolchain/typearmor-master"
        self.target_dir = './target_info'
        self.function_info = {}  # func_name:(func_start, func_end)
        self.func_name2addr = dict()
        self.func_addr2name = dict()
        self.func_line2addr = dict()
        self.func_addr2line = dict()
        self.ind_addr2source = {}
        self.variadic_over = set()  # variadic functions whose number of arguments are overestimated
        self.variadic_under = list()  # variadic functions whose number of arguments are underestimated
        self.typearmor_info = defaultdict(list)  # 1 indicate it is identified as variadic function
        self.typearmor_ind_info = dict()  # address of indirect call as the key, value is the number of argument for the indirect call
        self.readrdx = list()  # functions which read %RDX
        self.read63 = defaultdict(list)  # functions which read 64 bit to 32 bit
        self.reg_bitmap = defaultdict(list)

        self.icall_in_wrapper_taken = list()  # Indirect caller in wrapper function and there is no direct caller for this wrapper function
        self.icall_in_wrapper_dcall = list()  # Indirect caller in wrapper function and there are direct callers for this wrapper function
        self.icall_bet = list()

        self.icall_argPointer = defaultdict(list)  # indirect call whose argument is pointer to .data section
        self.icall_argImm = defaultdict(list)  # indirect call whose argument is immediate value

        self.icall_R13 = defaultdict(list)  # indirect call whose arguments read 16-bit to 32-bit register
        self.icall_R36 = defaultdict(list)  # indirect call whose arguments read 32-bit to 64-bit register

        self.icall_xor = defaultdict(list)  # Indirect callers whose arguments are passed using xor instructions

        self.ParaWidthOB = defaultdict(list)  # the recovered argument width at callee sites

        self.ArgWidthOB = defaultdict(list)  # the recovered argument width at caller sites

        self.ParaWidthGT = defaultdict(list)  # the groud truth of the argument width at the callee site

        self.ArgWidthGT = defaultdict(list)  # the groud truth of the argument width at the caller site

        self.ArgWidthGT_line = defaultdict(list)
        self.function_addr_name_type = dict()
        self.indirect_in_func = defaultdict(list)
        self.func_line2name = dict()
        self.llvm_fun_info = defaultdict(list)
        self.llvm_ind_info = dict()

        self.variadic_as_normal = 0
        self.variadic_as_normal_fun = list()
        self.normal_as_variadic = 0
        self.normal_as_variadic_fun = list()
        self.func_num_underestimation = list()
        self.func_num_overestimation = list()
        self.func_num_correct = list()
        self.func_num_underestimation_zero_parameter = list()
        self.func_num_underestimation_one = list()
        self.func_width_underestimization = defaultdict(list)
        self.func_width_overestimization = defaultdict(list)
        self.func_width_correct = defaultdict(list)

        self.ghidra_num_underestimation = list()
        self.ghidra_num_overestimation = list()
        self.ghidra_width_underestimization = defaultdict(list)
        self.ghidra_width_overestimization = defaultdict(list)

        self.ghidra_icall_num_underestimation = {}
        self.ghidra_icall_num_overestimation = {}

        self.ghidra_icall_width_underestimization = defaultdict(list)
        self.ghidra_icall_width_overestimization = defaultdict(list)

        self.icall_num_underestimation = {}
        self.icall_num_overestimation = {}
        self.icall_num_correct = defaultdict(list)
        self.icall_width_correct = defaultdict(list)
        self.icall_no_ground_truth = list()
        self.icall_width_underestimization = defaultdict(list)
        self.icall_width_overestimization = defaultdict(list)
        self.total_func = 0
        self.total_func_0 = 0
        self.total_icall = 0
        self.total_icall_0 = 0
        self.variadic_func = 0

    def find_last_colon(self, str_name):
        colon_index = 0
        for index in range(len(str_name) - 1, 0, -1):
            if str_name[index] == ':':
                return index
        # return 0
        return colon_index

    def find_dot(self, str_name):
        for index in range(len(str_name)):
            if str_name[index] == '.':
                return index
        return 0

    def get_function_info(self, binname):
        self.function_info = {}  # func_name:(func_start, func_end)
        cmd = "readelf -s -W " + binname + " |grep FUNC|awk '{print $2,$3, $8}'"
        with os.popen(cmd) as file:
            for line in file:
                line = line.split()
                # print(line)
                if len(line) > 2:
                    func_name = line[2]
                    # print func_name
                    func_start = int(line[0], 16)
                    func_end = func_start + int(line[1], 16)
                    # print func_start,func_end
                    if (func_start > 0 and func_start != func_end):
                        self.function_info[func_name] = (func_start, func_end)

    def readAsm(self, asmfile, file_name, icall2source):
        self.func_line2name = dict()
        self.func_name2addr = dict()
        self.func_addr2name = dict()
        self.func_line2addr = dict()
        self.func_addr2line = dict()
        self.ind_addr2source = {}

        func_name_pattern = re.compile("[0-9a-fA-F]{1,16}\s<\S*>:")
        # source_name_pattern = re.compile("/\S*")
        linecount = {}
        count = 0
        func_start = 0
        func_end = 0
        source_line = ''
        func_line = ''
        func_name_iner = " "
        find_bracket = 0

        source_inner = " "
        if os.path.isfile(icall2source):
            with open(icall2source) as f:
                for line in f:
                    line = line.rstrip()
                    line = line.split()
                    if len(line) > 2:
                        addr = int(line[0], 16)
                        func_name = line[1]
                        source_line = line[2]
                        self.ind_addr2source[addr] = (func_name, source_line)
            pass
        with open(asmfile, "r") as my_file:

            for line in my_file:
                m = func_name_pattern.match(line)

                line = line.rstrip()

                source_file_asm = line

                if 'gcc/O' in source_file_asm:
                    source_file_asm_list = source_file_asm.split('gcc')

                    line = source_file_asm_list[0] + 'clang/O0' + source_file_asm_list[1][3:]

                if (m != None):
                    # print "find function",line
                    first = 0
                    find_bracket = 0
                    linecount = {}
                    line_m = line.split(" ")
                    func_addr = int(line_m[0], 16)
                    func_name = line_m[1][1:len(line_m[1]) - 2]

                    if "constprop" in func_name:
                        dot_index = func_name.find(".constprop")
                        func_name = func_name[:dot_index]
                    # print "constprop **",func_name

                    self.func_addr2name[func_addr] = func_name
                    if func_name in self.function_info:
                        func_start = self.function_info[func_name][0]
                        func_end = self.function_info[func_name][1]

                if "/" in line and first == 0:
                    func_line = line.rstrip() + ";" + func_name

                    self.func_addr2line[func_addr] = func_line
                    self.func_line2name[func_line] = func_name
                    if func_line not in self.func_line2addr:
                        self.func_line2addr[func_line] = func_addr
                    first = 1

                if "/" in line:
                    source_line = line.rstrip()

                if "callq  *" in line:
                    # print line
                    line_q = line.split(":")
                    addr = int(line_q[0], 16)
                    # print(hex(addr))
                    # source_line = ''
                    if not os.path.isfile(icall2source):

                        cmd = "addr2line -e " + file_name + " " + str(hex(addr))

                        result = subprocess.check_output(cmd, shell=True)

                        # result2 = commands.getoutput(cmd).rstrip()

                        result = result.rstrip()

                        result2 = result.split()[0].decode()
                        # print(result2)

                        info = result2.split(":")

                        line_num = info[len(info) - 1]

                        if line_num.isdigit():
                            source_line = result2

                        source_file_asm = source_line

                        if 'gcc/O' in source_file_asm:
                            source_file_asm_list = source_file_asm.split('gcc')

                            source_line = source_file_asm_list[0] + 'clang/O0' + source_file_asm_list[1][3:]

                        if addr not in self.ind_addr2source:
                            # ind_addr2source[addr] = (source_inner,func_line,source_line_new)
                            self.ind_addr2source[addr] = (func_name, source_line)



        if not os.path.isfile(icall2source):
            with open(icall2source, 'w') as f:
                for addr in self.ind_addr2source:
                    (func_name, source_line) = self.ind_addr2source[addr]
                    f.write(str(hex(addr)) + ' ' + func_name + ' ' + source_line + "\n")

    def parseAsm(self, file_name, icall2source):

        asmfile = file_name + "-dis.txt"
        cmd = "objdump -ld " + file_name + " > " + asmfile
        os.system(cmd)
        self.get_function_info(file_name)
        self.readAsm(asmfile, file_name, icall2source)



    def read_ghidra_file(self, file_name):
        print("reading ghidra file " + file_name)
        ghidra_info = defaultdict(list)
        function_addr_name_type = dict()

        ParaWidthOB = defaultdict(list)  # the recovered argument width at callee sites

        ArgWidthOB = defaultdict(list)  # the recovered argument width at caller sites
        ghidra_ind_info = dict()

        with open(file_name, "r") as f:
            for line in f:
                line = line.rstrip()
                #print(line)
                if 'Function:' in line:
                    temp = line.split()
                    func_addr = int(temp[1],16)
                    parameterNum = int(temp[3])
                    #print("----- "+temp[1]+' '+str(parameterNum))
                    ghidra_info[func_addr].append(parameterNum)

                    if 'variadic' == temp[len(temp) -1]:
                        ghidra_info[func_addr].append(1)
                    else:
                        ghidra_info[func_addr].append(0)

                    #print(ghidra_info)
                    if len(temp) > 4:
                        for i in range(4, 4+parameterNum):
                            parameterWidth = int(temp[i])
                            ParaWidthOB[func_addr].append(parameterWidth)
                    #print(ParaWidthOB)
                elif 'CALLIND:' in line:
                    temp = line.split()
                    #print(temp)
                    icall_addr = int(temp[1],16)
                    argNum = int(temp[2])
                    #print(print("----- "+temp[1]+' '+str(argNum)))
                    ghidra_ind_info[icall_addr] = argNum
                    #print(ghidra_ind_info)
                    if len(temp) > 3:
                        for i in range(3,3+argNum):
                            argWidth = int(temp[i])
                            ArgWidthOB[icall_addr].append(argWidth)
                    #print(ArgWidthOB)

        #print(ghidra_info)

        return ghidra_info, ghidra_ind_info, ParaWidthOB, ArgWidthOB



    # parse info generated by typearmor
    def read_typearmor_file(self, file_name):
        print('reading typearmor result ' + file_name)
        self.variadic_over = set()
        typearmor_info = defaultdict(list)
        function_addr_name_type = dict()

        self.readrdx = list()  # functions which read %RDX
        self.read63 = defaultdict(list)  # functions which read 64 bit to 32 bit
        reg_bitmap = defaultdict(list)

        self.icall_in_wrapper_taken = list()  # Indirect caller in wrapper function and there is no direct caller for this wrapper function
        self.icall_in_wrapper_dcall = list()  # Indirect caller in wrapper function and there are direct callers for this wrapper function
        self.icall_bet = list()

        self.icall_argPointer = defaultdict(list)  # indirect call whose argument is pointer to .data section
        self.icall_argImm = defaultdict(list)  # indirect call whose argument is immediate value

        self.icall_R13 = defaultdict(list)  # indirect call whose arguments read 16-bit to 32-bit register
        self.icall_R36 = defaultdict(list)  # indirect call whose arguments read 32-bit to 64-bit register

        self.icall_xor = defaultdict(list)  # Indirect callers whose arguments are passed using xor instructions

        ParaWidthOB = defaultdict(list)  # the recovered argument width at callee sites

        ArgWidthOB = defaultdict(list)  # the recovered argument width at caller sites
        typearmor_ind_info = dict()


        # global typearmor_info, typearmor_ind_info
        with open(file_name, "r") as f:
            lines = f.readlines()
            line_count = 0

            if line_count < len(lines):

                # for line_count in range(len(lines)):
                line = lines[line_count]

                while ("[varargs]" not in line):
                    line_count += 1
                    line = lines[line_count]

                if "[varargs]" in lines[line_count]:
                    line_count += 1
                    next_line = lines[line_count]

                    while ("[args]" not in next_line and line_count < len(lines)):
                        splitted_next_line = next_line.split()
                        if len(splitted_next_line) > 1:
                            function_addr = splitted_next_line[0]
                            function_name = splitted_next_line[3]
                            parameter_number = splitted_next_line[2]

                            real_function_name = function_name[1:len(function_name) - 1]

                            if "variadic_over" in next_line:
                                self.variadic_over.add(int(function_addr, 16))

                            # if real_function_name not in typearmor_info:
                            typearmor_info[int(function_addr, 16)].append(int(parameter_number))
                            typearmor_info[int(function_addr, 16)].append(1)
                            # function_name_addr[real_function_name] = int(function_addr,16)
                            function_addr_name_type[int(function_addr, 16)] = real_function_name
                        # print function_name, parameter_number
                        line_count += 1
                        next_line = lines[line_count]
                if "[args]" in lines[line_count]:
                    # line_count += 1
                    next_line = lines[line_count]
                    while ("[icall-args]" not in next_line and line_count < len(lines)):
                        splitted_next_line = next_line.split()
                        # print next_line
                        if len(splitted_next_line) > 1:
                            # print(splitted_next_line)
                            function_addr = int(splitted_next_line[0], 16)
                            # function_name = splitted_next_line[3]
                            parameter_number = int(splitted_next_line[2])

                            function_name_start_index = next_line.find('(')
                            function_name_end_index = next_line.rfind(')')

                            real_function_name = next_line[function_name_start_index + 1:function_name_end_index]

                            width_info = next_line[function_name_end_index + 1:].split()
                            # print width_info, next_line

                            if len(width_info) > (parameter_number):
                                for i in range(parameter_number):
                                    parameterWidth = int(width_info[i])
                                    ParaWidthOB[function_addr].append(parameterWidth)

                            if len(width_info) > (parameter_number):
                                for i in range(parameter_number, len(width_info)):
                                    if "readRDX" in width_info[i]:
                                        self.readrdx.append(function_addr)
                                    if "read63" in width_info[i]:
                                        r13s = width_info[i].split('{')
                                        r13 = r13s[1]
                                        r13_index = r13.split(',')
                                        for j in range(len(r13_index) - 1):
                                            index = int(r13_index[j])
                                            if index not in self.read63[function_addr]:
                                                # icall_R13[indirect_addr].append(index)
                                                self.read63[function_addr].append(index)
                                    if "reg_bitmap:" in width_info[i]:
                                        bitmap = width_info[i].split(':')[1]
                                        # print(bitmap)
                                        for j in range(len(bitmap)):
                                            reg_bitmap[function_addr].append(int(bitmap[j]))

                            if function_addr not in function_addr_name_type:
                                function_addr_name_type[function_addr] = real_function_name
                            if function_addr not in typearmor_info:
                                typearmor_info[function_addr].append(parameter_number)
                                typearmor_info[function_addr].append(0)
                            # print real_function_name,parameter_number
                        line_count += 1
                        # print(line_count)
                        if line_count < len(lines):
                            next_line = lines[line_count]
                        else:
                            line_count = line_count - 1
                            break
                if "[icall-args]" in lines[line_count]:
                    # line_count += 1
                    next_line = lines[line_count]
                    while ("[plts]" not in next_line and line_count < len(lines)):
                        splitted_next_line = next_line.split()
                        if len(splitted_next_line) > 1:
                            indirect_addr = int(splitted_next_line[0], 16)
                            function_name = splitted_next_line[3][::-1]
                            argument_number = int(splitted_next_line[2])
                            index = self.find_dot(function_name)
                            function_name = function_name[index + 1:]
                            real_function_name = function_name[::-1][1:len(function_name)]

                            function_name_start_index = next_line.find('(')
                            function_name_end_index = next_line.rfind(')')

                            width_info = next_line[function_name_end_index + 1:].split()
                            # print width_info,next_line
                            if len(width_info) > (argument_number):
                                for i in range(argument_number):
                                    if len(width_info) >= argument_number:
                                        if width_info[i].isdigit():
                                            argumentWidth = int(width_info[i])
                                            ArgWidthOB[indirect_addr].append(argumentWidth)

                            if len(width_info) > (argument_number):
                                for i in range(argument_number, len(width_info)):
                                    if "Icall" in width_info[i]:
                                        self.icall_in_wrapper_taken.append(indirect_addr)
                                    if "Dcall" in width_info[i]:
                                        self.icall_in_wrapper_dcall.append(indirect_addr)
                                    if "bet" in width_info[i]:
                                        self.icall_bet.append(indirect_addr)

                                    if "ImmArg" in width_info[i]:
                                        immargs = width_info[i].split('{')
                                        immarg = immargs[1]
                                        immarg_index = immarg.split(',')
                                        for j in range(len(immarg_index) - 1):
                                            index = int(immarg_index[j])
                                            if index not in self.icall_argImm[indirect_addr]:
                                                self.icall_argImm[indirect_addr].append(index)

                                    if "PointerArg" in width_info[i]:
                                        pointerargs = width_info[i].split('{')
                                        pointerarg = pointerargs[1]
                                        pointerarg_index = pointerarg.split(',')
                                        for j in range(len(pointerarg_index) - 1):
                                            index = int(pointerarg_index[j])
                                            if index not in self.icall_argPointer[indirect_addr]:
                                                self.icall_argPointer[indirect_addr].append(index)

                                    if "13Arg" in width_info[i]:
                                        args13 = width_info[i].split('{')
                                        arg13 = args13[1]
                                        arg13_index = arg13.split(',')
                                        for j in range(len(arg13_index) - 1):
                                            index = int(arg13_index[j])
                                            if index not in self.icall_R13[indirect_addr]:
                                                self.icall_R13[indirect_addr].append(index)

                                    if "36Arg" in width_info[i]:
                                        args36 = width_info[i].split('{')
                                        arg36 = args36[1]
                                        arg36_index = arg36.split(',')
                                        for j in range(len(arg36_index) - 1):
                                            index = int(arg36_index[j])
                                            if index not in self.icall_R36[indirect_addr]:
                                                self.icall_R36[indirect_addr].append(index)

                                    if "Xor" in width_info[i]:
                                        argsxor = width_info[i].split('{')
                                        argxor = argsxor[1]
                                        argxor_index = argxor.split(',')
                                        for j in range(len(argxor_index) - 1):
                                            index = int(argxor_index[j])
                                            if index not in self.icall_xor[indirect_addr]:
                                                self.icall_xor[indirect_addr].append(index)

                            typearmor_ind_info[indirect_addr] = argument_number
                        line_count += 1
                        # print(line_count)
                        if line_count < len(lines):
                            next_line = lines[line_count]
                        else:
                            line_count = line_count - 1
                            break

        #print(typearmor_info)
        return typearmor_info, typearmor_ind_info, ParaWidthOB, ArgWidthOB

    # parse info generated by llvm
    def read_llvm_file(self, file_name):
        print('reading groundTruth ' + file_name)
        func_llvm2line = dict()
        ParaWidthGT = defaultdict(list)
        llvm_fun_info = defaultdict(list)
        llvm_ind_info = dict()
        ArgWidthGT = defaultdict(list)

        with open(file_name, "r") as f:
            lines = f.readlines()
            # line_count = 0
            object_file_info = defaultdict(list)
            for line_count in range(len(lines)):
                line = lines[line_count]
                line_count += 1

                if "Function:" in line:
                    line = line.rstrip('\n')
                    line = line.split()
                    if len(line) > 1:

                        function_name = line[1]

                        '''
						old_function_name = function_name
						if function_name.find('.') != -1:
							
							number = function_name[function_name.find('.')+1:]
							if number.isdigit():
								function_name = function_name[:function_name.find('.')]
						'''

                        source_file = line[len(line) - 1]

                        if source_file.isdigit():
                            source_file = ""
                            source_info = source_file
                            source_file_line = 0
                        else:
                            source_file_index = self.find_last_colon(source_file)
                            if source_file_index != -1:
                                source_info = source_file[:source_file_index]
                                source_file_line = int(source_file[source_file_index + 1:])
                            else:
                                source_info = source_file
                                source_file_line = 0

                        #source_info = source_info.replace('/home/yanlin/my-projects/obfuscation-arg/python-script/', '')
                        parameter_number = line[len(line) - 2]

                        found = 0

                        for line_asm in self.func_line2name:
                            asm_name = self.func_line2name[line_asm]
                            asm_comma = line_asm.find(";")
                            # print(line_asm)

                            if asm_comma != -1:
                                asm_file_index = self.find_last_colon(line_asm[:asm_comma])
                                if asm_file_index != -1:
                                    asm_info = line_asm[:asm_file_index]

                                    asm_file_line = line_asm[asm_file_index + 1:asm_comma]
                                    if asm_file_line.isdigit():
                                        asm_file_line = int(asm_file_line)
                                    else:
                                        asm_file_line = 0
                                else:
                                    asm_info = line_asm
                                    asm_file_line
                            else:
                                asm_info = line_asm
                                asm_file_line = 0

                            c = source_file_line - asm_file_line
                            # print asm_info,source_info

                            temp_index = source_info.find("//")
                            # print(temp_index)

                            source_info = source_info[temp_index + 1:]

                            index = asm_info.find(source_info)
                            # print(source_info, asm_info)

                            if source_info == asm_info:
                                # print(source_info, asm_info)
                                # print(asm_name, function_name)
                                # print(source_file_line, asm_file_line)
                                if asm_name == function_name:
                                    if line_asm in self.func_line2addr:
                                        func_addr = self.func_line2addr[line_asm]
                                        # print(func_addr)

                                        parameter_number = int(parameter_number)
                                        for j in range(len(line) - 2):
                                            width_str = line[2 + j]
                                            if width_str in ["*", "long"]:
                                                width = 8
                                                ParaWidthGT[func_addr].append(width)
                                            elif width_str == "int":
                                                width = 4
                                                ParaWidthGT[func_addr].append(width)
                                            elif width_str == "short":
                                                width = 2
                                                ParaWidthGT[func_addr].append(width)
                                            elif width_str in ["char", "_Bool"]:
                                                width = 1
                                                ParaWidthGT[func_addr].append(width)
                                            else:
                                                j += 1

                                        llvm_fun_info[func_addr].append(parameter_number)

                                        if "variadic" in line[len(line) - 3]:
                                            llvm_fun_info[func_addr].append(1)
                                        else:
                                            llvm_fun_info[func_addr].append(0)
                                        found = 1
                                        break

                        if line_count < len(lines):
                            next_line = lines[line_count]

                            # srcLine_info={}
                            icall_count = 0
                            while ("Ind-call: " in next_line):
                                indirect_info = next_line.rstrip("\n")
                                indirect_info = next_line.split()
                                icall_count += 1

                                ind_arg_count = int(indirect_info[len(indirect_info) - 2])

                                srcLine = indirect_info[len(indirect_info) - 1].rstrip()

                                if (function_name, srcLine) not in llvm_ind_info:
                                    llvm_ind_info[(function_name, srcLine)] = ind_arg_count

                                    for j in range(len(indirect_info) - 2):
                                        width_str = indirect_info[1 + j]

                                        if width_str in ["*", "long"]:
                                            width = 8
                                            ArgWidthGT[(function_name, srcLine)].append(width)
                                        elif width_str == "int":
                                            width = 4
                                            ArgWidthGT[(function_name, srcLine)].append(width)
                                        elif width_str == "short":
                                            width = 2
                                            ArgWidthGT[(function_name, srcLine)].append(width)
                                        elif width_str in ["char", "_Bool"]:
                                            width = 1
                                            ArgWidthGT[(function_name, srcLine)].append(width)
                                        else:
                                            j += 1


                                else:
                                    icall_arg = llvm_ind_info[(function_name, srcLine)]

                                    if icall_arg != ind_arg_count:
                                        llvm_ind_info.pop((function_name, srcLine))
                                        if (function_name, srcLine) in ArgWidthGT:
                                            ArgWidthGT.pop((function_name, srcLine), None)

                                line_count += 1
                                if line_count < len(lines):
                                    next_line = lines[line_count]
                                else:
                                    line_count = line_count - 1
                                    break

        # print(llvm_fun_info)
        return llvm_fun_info, llvm_ind_info, ParaWidthGT, ArgWidthGT

    def run_typearmor(self, bin_path):
        cwd = os.getcwd()

        # os.environ["DYNINST_ROOT"] = '/home/yanlin/toolchain/dyninst-9.3.1'
        # os.environ["DYNINST_LIB"] = os.environ["DYNINST_ROOT"] + '/install/lib'
        # os.environ["DYNINSTAPI_RT_LIB"] = os.environ["DYNINST_LIB"] + "/libdyninstAPI_RT.so"
        # os.environ["LD_LIBRARY_PATH"] = os.getcwd()
        # os.environ["LD_LIBRARY_PATH"] += os.environ["DYNINST_LIB"]

        orig_bin = os.path.basename(bin_path)

        os.chdir(self.type_armor_path + "/server-bins")

        # copy the executable into typearmor
        cmd = "cp " + bin_path + " " + orig_bin

        os.system(cmd)

        cmd = "bash " + self.type_armor_path + "/run-ta-static.sh " + orig_bin

        os.system(cmd)

        # os.system('rm -f '+orig_bin)
        # os.system('rm -f *.csv')

        os.system('rm -f *')

        os.chdir(cwd)

    # compare the result obtained by typearmor
    def obtain_signature(self, bin_path, groundtruth_path, compiler, opt, transform):
        cwd = os.getcwd()
        target_dir = os.path.join(self.target_dir, transform)
        target_dir = os.path.join(target_dir, compiler)
        target_dir = os.path.join(target_dir, opt)
        cmd = "mkdir -p " + target_dir
        os.system(cmd)

        orig_bin = os.path.basename(bin_path)

        cmd = "mkdir -p " + os.path.join(target_dir, orig_bin)
        os.system(cmd)

        llvm_path = orig_bin + "-llvm-info.txt"
        typearmor_path = orig_bin + "-typearmor.txt"

        temp = os.path.join(target_dir, orig_bin)

        if  not os.path.isfile(os.path.join(temp, typearmor_path)):
            self.run_typearmor(bin_path)

            os.chdir(os.path.join(target_dir, orig_bin))

            os.system('sudo chown yanlin:yanlin ' + self.type_armor_path + "/out/" + "binfo." + orig_bin)

            cmd = "mv " + self.type_armor_path + "/out/" + "binfo." + orig_bin + " " + typearmor_path
            os.system(cmd)

            cmd = "cp " + bin_path + " " + orig_bin
            os.system(cmd)
            print(cmd)

            os.system('cp ' + groundtruth_path + " " + llvm_path)



            os.chdir(cwd)

    def read_typearmor_signature(self, bin_path, groundtruth_path, compiler, opt, transform):
        cwd = os.getcwd()

        target_dir = os.path.join(self.target_dir, transform)
        target_dir = os.path.join(target_dir, compiler)
        target_dir = os.path.join(target_dir, opt)

        orig_bin = os.path.basename(bin_path)
        llvm_path = orig_bin + "-llvm-info.txt"
        typearmor_path = orig_bin + "-typearmor.txt"

        if os.path.isdir(os.path.join(target_dir, orig_bin)):
            print(target_dir)
            os.chdir(os.path.join(target_dir, orig_bin))
            self.parseAsm(orig_bin, 'icall2source.txt')

            if os.path.isfile(typearmor_path) and os.path.isfile(llvm_path):
                try:
                    typearmor_info, typearmor_ind_info, ParaWidthOB, ArgWidthOB = self.read_typearmor_file(typearmor_path)

                    llvm_fun_info, llvm_ind_info, ParaWidthGT, ArgWidthGT = self.read_llvm_file(llvm_path)

                    self.typearmor_info = typearmor_info
                    self.llvm_fun_info = llvm_fun_info
                    self.ParaWidthGT = ParaWidthGT
                    self.ParaWidthOB = ParaWidthOB
                    self.ArgWidthOB = ArgWidthOB
                    self.ArgWidthGT = ArgWidthGT


                    self.compare_func(llvm_fun_info, typearmor_info, ParaWidthGT, ParaWidthOB)
                    self.compare_ind(llvm_ind_info, typearmor_ind_info, ArgWidthGT, ArgWidthOB)

                    self.ghidra_num_overestimation = self.func_num_overestimation 
                    self.ghidra_num_underestimation = self.func_num_underestimation 
                    self.ghidra_icall_num_overestimation = self.icall_num_overestimation 
                    self.ghidra_icall_num_underestimation = self.icall_num_underestimation

                except:
                    print('cannot process')

            os.chdir(cwd)


    def read_ghidra_signature(self, bin_path, groundtruth_path, compiler, opt, transform):
        #self.typearmor_info = defaultdict(list)
        #self.ParaWidthOB = defaultdict(list)  # the recovered argument width at callee sites

        #self.ArgWidthOB = defaultdict(list)  # the recovered argument width at caller sites
        #self.llvm_fun_info = defaultdict(list)
        #self.llvm_ind_info = dict()
        #self.ParaWidthGT = defaultdict(list)  # the groud truth of the argument width at the callee site

        #self.ArgWidthGT = defaultdict(list)  # the groud truth of the argument width at the caller site

        cwd = os.getcwd()

        target_dir = os.path.join(self.target_dir, transform)
        target_dir = os.path.join(target_dir, compiler)
        target_dir = os.path.join(target_dir, opt)

        orig_bin = os.path.basename(bin_path)
        llvm_path = orig_bin + "-llvm-info.txt"
        ghidra_path = orig_bin + "-ghidra.txt"
        if os.path.isdir(os.path.join(target_dir, orig_bin)):
            print(target_dir)
            os.chdir(os.path.join(target_dir, orig_bin))

            self.parseAsm(orig_bin, 'icall2source.txt')

            if os.path.isfile(ghidra_path) and os.path.isfile(llvm_path):
                try:
                    llvm_fun_info, llvm_ind_info, ParaWidthGT, ArgWidthGT = self.read_llvm_file(llvm_path)
                    ghidra_info, ghidra_ind_info, ghidra_ParaWidthOB, ghidra_ArgWidthOB = self.read_ghidra_file(ghidra_path)
                    
                    #print("****************")
                    #print(ghidra_info)
                    self.typearmor_info = ghidra_info
                    self.llvm_fun_info = llvm_fun_info
                    self.ParaWidthGT = ParaWidthGT
                    self.ParaWidthOB = ghidra_ParaWidthOB
                    self.ArgWidthOB = ghidra_ArgWidthOB
                    self.ArgWidthGT = ArgWidthGT

                    #print(self.typearmor_info)

                    self.compare_func(llvm_fun_info, ghidra_info, ParaWidthGT, ghidra_ParaWidthOB)
                    self.compare_ind(llvm_ind_info, ghidra_ind_info, ArgWidthGT, ghidra_ArgWidthOB)


                except:
                    print('cannot process')


            os.chdir(cwd)

    # self.compare_func(llvm_fun_info, typearmor_info, ParaWidthGT, ParaWidthOB)
    # READ THE SIGNATURE FILES OBTINAED BY LLVM AND TYPEARMOR
    def read_signature_file(self, bin_path, groundtruth_path, compiler, opt, transform, ghidra='false'):
        cwd = os.getcwd()

        target_dir = os.path.join(self.target_dir, transform)
        target_dir = os.path.join(target_dir, compiler)
        target_dir = os.path.join(target_dir, opt)

        orig_bin = os.path.basename(bin_path)
        llvm_path = orig_bin + "-llvm-info.txt"
        typearmor_path = orig_bin + "-typearmor.txt"
        ghidra_path = orig_bin + "-ghidra.txt"
        print(target_dir)
        if os.path.isdir(os.path.join(target_dir, orig_bin)):
            print(target_dir)
            os.chdir(os.path.join(target_dir, orig_bin))
            cmd = "cp " + bin_path + " " + orig_bin
            os.system(cmd)

            self.parseAsm(orig_bin, 'icall2source.txt')



            if not os.path.isfile(llvm_path):
                os.system('cp ' + groundtruth_path + " " + llvm_path)

            if os.path.isfile(typearmor_path) and os.path.isfile(llvm_path):
                print("****************",typearmor_path)

                try:
                    typearmor_info, typearmor_ind_info, ParaWidthOB, ArgWidthOB = self.read_typearmor_file(typearmor_path)

                    llvm_fun_info, llvm_ind_info, ParaWidthGT, ArgWidthGT = self.read_llvm_file(llvm_path)

                    if ghidra == 'true':
                        ghidra_info, ghidra_ind_info, ghidra_ParaWidthOB, ghidra_ArgWidthOB = self.read_ghidra_file(ghidra_path)

                    if ghidra == 'true':
                        self.typearmor_info = ghidra_info
                        self.llvm_fun_info = llvm_fun_info
                        self.ParaWidthGT = ParaWidthGT
                        self.ParaWidthOB = ghidra_ParaWidthOB
                        self.ArgWidthOB = ghidra_ArgWidthOB
                        self.ArgWidthGT = ArgWidthGT
                    else:
                        self.typearmor_info = typearmor_info
                        self.llvm_fun_info = llvm_fun_info
                        self.ParaWidthGT = ParaWidthGT
                        self.ParaWidthOB = ParaWidthOB
                        self.ArgWidthOB = ArgWidthOB
                        self.ArgWidthGT = ArgWidthGT

                    if ghidra == 'true':

                        self.compare_func(llvm_fun_info, typearmor_info, ParaWidthGT, ParaWidthOB)
                        self.compare_ind(llvm_ind_info, typearmor_ind_info, ArgWidthGT, ArgWidthOB)

                        self.ghidra_num_overestimation = self.func_num_overestimation 
                        self.ghidra_num_underestimation = self.func_num_underestimation 
                        self.ghidra_icall_num_overestimation = self.icall_num_overestimation 
                        self.ghidra_icall_num_underestimation = self.icall_num_underestimation


                        self.compare_func(llvm_fun_info, ghidra_info, ParaWidthGT, ghidra_ParaWidthOB)
                        self.compare_ind(llvm_ind_info, ghidra_ind_info, ArgWidthGT, ghidra_ArgWidthOB)
                    
                        pass
                    else:

                        self.compare_func(llvm_fun_info, typearmor_info, ParaWidthGT, ParaWidthOB)
                        self.compare_ind(llvm_ind_info, typearmor_ind_info, ArgWidthGT, ArgWidthOB)
                except:
                    #pass
                    print('cannot process')

            os.chdir(cwd)

    def compare_func(self, llvm_fun_info, typearmor_info, ParaWidthGT, ParaWidthOB):
        self.variadic_as_normal = 0
        self.variadic_as_normal_fun = list()
        self.normal_as_variadic = 0
        self.normal_as_variadic_fun = list()
        self.func_num_underestimation = list()
        self.func_num_overestimation = list()
        self.func_num_correct = list()
        self.func_num_underestimation_zero_parameter = list()
        self.func_num_underestimation_one = list()
        self.func_width_underestimization = defaultdict(list)
        self.func_width_overestimization = defaultdict(list)
        self.func_width_correct = defaultdict(list)
        self.total_func = 0
        self.total_func_0 = 0
        self.variadic_func = 0
        self.variadic_under = list()

        base_count = 0

        for i in llvm_fun_info:
            # print i
            if i in typearmor_info:
                self.total_func += 1


                llvm_count = llvm_fun_info[i][0]
                if llvm_count == 0:
                    self.total_func_0 += 1
                llvm_variadic = llvm_fun_info[i][1]
                typearmor_count = typearmor_info[i][0]
                typearmor_variadic = typearmor_info[i][1]
                if llvm_variadic == 0 and typearmor_variadic == 1:
                    self.normal_as_variadic_fun.append(i)
                    self.normal_as_variadic += 1
                if llvm_variadic == 1 and typearmor_variadic == 0:
                    self.variadic_as_normal_fun.append(i)
                    self.variadic_as_normal += 1

                if llvm_variadic == 1:
                    self.variadic_func += 1

                if llvm_count > typearmor_count:
                    base_count = typearmor_count
                    if llvm_count <= 6:
                        self.func_num_underestimation.append(i)
                        if llvm_variadic == 1 and typearmor_variadic == 1:
                            self.variadic_under.append(i)
                    elif llvm_count > 6 and typearmor_count < 6:
                        self.func_num_underestimation.append(i)
                        if llvm_variadic == 1 and typearmor_variadic == 1:
                            self.variadic_under.append(i)
                    elif llvm_count > 6 and typearmor_count == 6:
                        self.func_num_correct.append(i)

                elif llvm_count < typearmor_count:
                    base_count = llvm_count
                    self.func_num_overestimation.append(i)
                else:
                    self.func_num_correct.append(i)
                    base_count = llvm_count
                    if llvm_count == 0:
                        self.func_width_correct[i].append(0)
                if typearmor_count == 0 and llvm_count > typearmor_count:
                    if typearmor_variadic == 0:
                        self.func_num_underestimation_zero_parameter.append(i)
                if typearmor_count == 1 and llvm_count > typearmor_count:
                    self.func_num_underestimation_one.append(i)

                # compare width
                # print(base_count)


                if i in ParaWidthGT:
                    if i in ParaWidthOB:
                        base_count = min(len(ParaWidthGT[i]), len(ParaWidthOB[i]))
                        # print("base_count:", base_count)

                        for q in range(base_count):
                            widthGT = ParaWidthGT[i][q]
                            widthOB = ParaWidthOB[i][q]
                            if widthOB == 9:
                                widthOB = 0

                            if widthGT > widthOB:
                                self.func_width_underestimization[i].append(q + 1)

                            if widthGT < widthOB:
                                self.func_width_overestimization[i].append(q + 1)

                            if widthGT == widthOB:
                                #if i not in self.func_width_correct:
                                self.func_width_correct[i].append(q + 1)

    def compare_ind(self, llvm_ind_info, typearmor_ind_info, ArgWidthGT, ArgWidthOB):
        self.icall_num_underestimation = {}
        self.icall_num_overestimation = {}
        self.icall_num_correct = defaultdict(list)
        self.icall_width_correct = defaultdict(list)
        self.icall_no_ground_truth = list()
        self.icall_width_underestimization = defaultdict(list)
        self.icall_width_overestimization = defaultdict(list)
        self.total_icall = 0
        self.total_icall_0 = 0

        for addr in self.ind_addr2source:

            (func_name, srcLine) = self.ind_addr2source[addr]
            srcLine_old = srcLine
            find = 0
            base_count = 0

            if addr in typearmor_ind_info:
                typearmor_count = typearmor_ind_info[addr]
                if (func_name, srcLine) in llvm_ind_info:
                    self.total_icall += 1
                    llvm_count = llvm_ind_info[(func_name, srcLine)]
                    if llvm_count == 0:
                        self.total_icall_0 += 1
                    if llvm_count > typearmor_count:
                        if llvm_count <= 6:
                            self.icall_num_underestimation[addr] = (llvm_count, typearmor_count)
                        elif llvm_count > 6 and typearmor_count < 6:
                            self.icall_num_underestimation[addr] = (llvm_count, typearmor_count)
                        elif llvm_count > 6 and typearmor_count == 6:
                            self.icall_num_correct[addr].append(llvm_count)

                    elif llvm_count < typearmor_count:
                        # base_count = llvm_count
                        self.icall_num_overestimation[addr] = (llvm_count, typearmor_count)
                    elif llvm_count == typearmor_count:
                        self.icall_num_correct[addr].append(llvm_count)
                        if llvm_count == 0:
                            self.icall_width_correct[addr].append(0)

                    base_count = min(llvm_count, typearmor_count)

                    # compare argument width
                    if addr in ArgWidthOB:
                        if (func_name, srcLine) in ArgWidthGT:
                            base_count = min(len(ArgWidthOB[addr]), len(ArgWidthGT[(func_name, srcLine)]))

                            for i in range(base_count):
                                # print "***",src_t,ArgWidthGT[src_t][i]
                                if ArgWidthGT[(func_name, srcLine)][i] < ArgWidthOB[addr][i]:
                                    self.icall_width_overestimization[addr].append(i + 1)
                                elif ArgWidthGT[(func_name, srcLine)][i] > ArgWidthOB[addr][i]:
                                    self.icall_width_underestimization[addr].append(i + 1)
                                else:
                                    self.icall_width_correct[addr].append(i + 1)

    # return the obtained signature
    def get_llvm_func_info(self):
        return self.llvm_fun_info

    def get_llvm_ind_info(self):
        return self.llvm_ind_info

    def get_typearmor_func_info(self):
        return self.typearmor_info

    def get_typearmor_ind_info(self):
        return self.typearmor_ind_info

    def get_parawidthGT(self):
        return self.ParaWidthGT

    def get_parawidthOB(self):
        return self.ParaWidthOB

    def get_argwidthGT(self):
        return self.ArgWidthGT

    def get_argwidthOB(self):
        return self.ArgWidthOB

    # clear the obtained signature
    def clear_llvm_func_info(self):
        self.llvm_fun_info = defaultdict(list)

    def clear_llvm_ind_info(self):
        self.llvm_ind_info = dict()

    def clear_typearmor_func_info(self):
        self.typearmor_info = defaultdict(list)

    def clear_typearmor_ind_info(self):
        self.typearmor_ind_info = dict()

    def clear_parawidthGT(self):
        self.ParaWidthGT = defaultdict(list)

    def clear_parawidthOB(self):
        self.ParaWidthOB = defaultdict(list)

    def clear_argwidthGT(self):
        self.ArgWidthGT = defaultdict(list)

    def get_argwidthOB(self):
        self.ArgWidthOB = defaultdict(list)

    def get_func_num_underestimation(self):
        return self.func_num_underestimation

    def get_func_num_overestimation(self):
        return self.func_num_overestimation

    def get_func_num_correct(self):
        return self.func_num_correct

    def get_funcaddr_name(self):
        return self.func_addr2name

    def get_icall_num_underestimation(self):
        return self.icall_num_underestimation

    def get_icall_num_overestimation(self):
        return self.icall_num_overestimation

    def get_icall_num_correct(self):
        return self.icall_num_correct

    def get_variadic_under(self):
        return self.variadic_under
