import json
import sys
import os
import string
from ghidra.program.model.pcode import PcodeOp
#import ghidra.program.model.pcode.PcodeOpAST
import ghidra.program.database.DatabaseObject
from ghidra.program.model.lang.OperandType import SCALAR, REGISTER,INDIRECT
from collections import defaultdict
from ghidra.program.model.listing import VariableFilter
from  ghidra.program.model.listing import *
import ghidra.program.model.symbol.Symbol
from ghidra.program.model.pcode import *
from  ghidra.program.model.symbol import SymbolType;
import ghidra.program.database.symbol.NamespaceManager;
import ghidra.program.database.symbol.SymbolManager;
#from  ghidra.app.script.GhidraScript import *
from ghidra.app.script import GhidraScript
from ghidra.util.task import ConsoleTaskMonitor
import ghidra.framework.options.ToolOptions
import ghidra.app.script.GhidraState
import ghidra.framework.plugintool.util.OptionsService;

args = getScriptArgs()
response_dict = dict()

# if len(args) < 1:
# print("usage: ./function-signature-analysis.py output_path")
# sys.exit(0)

decompInterface = ghidra.app.decompiler.DecompInterface()
decompInterface.openProgram(currentProgram)

#setAnalysisOption(currentProgram, "Decompiler Parameter ID", "true");
# setAnalysisOption(currentProgram, "Condense Filler Bytes", "true");
# setAnalysisOption(currentProgram, "Variadic Function Signature Override", "true");

bin_path = currentProgram.getExecutablePath()
ori_bin = os.path.basename(bin_path)
cwd = os.getcwd()

output_folder = os.path.join(cwd, 'ghidra-analysis-out/signature')
os.system("mkdir -p " + output_folder)
output_path = os.path.join(output_folder, ori_bin+".txt")

fHandler = open(output_path,'w')

def getPcodeOpIterator(high):
	return high.getPcodeOps()


def getSignatures(op):
    argument = list()

    argNum = op.getNumInputs()
    width_info = list()
    #argument.append(argNum - 1)
    for i in range(1, argNum):
        vn = op.getInput(i);
        if vn:
            dt = vn.getHigh().getDataType()

            size = vn.getHigh().getSize()
            
            if dt:
                name = dt.getName()
                #print >> fHandler, name,
                if name == 'float' or name == 'double':
                    argNum = argNum - 1

                else:
                    width_info.append(size)
            else:
                width_info.append(0)
        else:
            width_info.append(0)

    argument.append(argNum - 1)

    for size in width_info:
        argument.append(size)

    return argument

functionIterator = currentProgram.getFunctionManager().getFunctions(True)
decompiledFunc = list()
for function in functionIterator:
    indirect_call_info = defaultdict(list)

    # decompileResults = decompInterface.decompileFunction(
    # function, 30, monitor)

    setAnalysisOption(currentProgram, "Decompiler Parameter ID", "true");

    decompileResults = decompInterface.decompileFunction(function, 0, ConsoleTaskMonitor())

    fName = function.getName()
    address = function.getEntryPoint()

    if decompileResults.decompileCompleted():
        decompiledFunction = decompileResults.getDecompiledFunction()
        decompiled = decompiledFunction.getSignature()
        highFunction = decompileResults.getHighFunction();

        print >> fHandler, "Function:",
        print >> fHandler, str(function.getEntryPoint()),
        print >> fHandler, function.getName(),

        FunctionPrototype = highFunction.getFunctionPrototype()

        paramNum = FunctionPrototype.getNumParams()
        paramType = list()

        for i in range(paramNum):
            highParam = FunctionPrototype.getParam(i)

            # print >> fHandler, "highParam: ", highParam

            # highSym = highParam.getSymbol()

            symType = highParam.getDataType()
            size = highParam.getSize()

            name = symType.getName()

            paramType.append((symType, size, name))

        width_info = list()
        # print >> fHandler, symType,

        #print >> fHandler, paramNum,

        for (symType, size, name) in paramType:
            if name == 'float' or name == 'double':
                paramNum = paramNum - 1
            else:
                width_info.append(size)
                #print >> fHandler, size, symType, name
        print >> fHandler, paramNum,

        for size in width_info:
            print >> fHandler, size, 

        if FunctionPrototype.isVarArg():
            print >> fHandler, 'variadic',

        print >> fHandler

        '''
        if FunctionPrototype.hasThisPointer():
            print >> fHandler, "hasThisPointer"

        
        
        print >> fHandler, "\tretType: ",
        # get return type
        if FunctionPrototype.hasNoReturn():
            print >> fHandler, "No return"

        else:
            retType = FunctionPrototype.getReturnType()
            print >> fHandler, retType
        '''
        #print >> fHandler, "\tsignature ->", paramType

        opiter = getPcodeOpIterator(highFunction)
        count = 0
        while opiter.hasNext():
            op = opiter.next()

            # if op.isDead():
            # continue

            opcode = op.getOpcode()

            '''param index #0 is the call target address, skip it, start at 1, the 0th parameter'''

            # SEXT
            # if opcode == PcodeOp.INT_SEXT:
            # opAddr = op.getSeqnum().getTarget();
            # print("SEXT ", opAddr)

            # indirect call
            if opcode == PcodeOp.CALLIND:
                opAddr = op.getSeqnum().getTarget();

                '''
                funcAddress = op.getInput(0);
                if funcAddress.getDef().getOpcode() == PcodeOp.PTRSUB:
                    struct = funcAddress.getDef().getInput(0)
                    field = funcAddress.getDef().getInput(1)
                '''

                argument = getSignatures(op)

                # output:
                output = op.getOutput()
                output_list = list()
                if output:
                    dt = output.getHigh().getDataType()
                    size = output.getHigh().getSize()
                    output_list.append((dt, size))

                print >> fHandler, "\tCALLIND: ", opAddr, #signature, "; output: ", output_list

                for item in argument:
                    print >> fHandler, item,

                print >> fHandler

