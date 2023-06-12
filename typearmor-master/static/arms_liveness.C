/*
 * Copyright 2017, Victor van der Veen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "PatchCommon.h"
#include "PatchMgr.h"
#include "PatchModifier.h"

#include "Visitor.h"
#include <sstream>

using namespace std;
using namespace Dyninst;
using namespace Dyninst::PatchAPI;
using namespace Dyninst::ParseAPI;
using namespace Dyninst::InstructionAPI;
using namespace Dyninst::SymtabAPI;

#include "defs.h" 
#include "arms_bb.h"
#include "arms_edge.h" 
#include "arms_function.h" 
#include "arms_liveness.h"

#include <liveness.h>
//#define DEBUG
//#define DDEBUG

/* Possible strategy types */
#define STRATEGY_CONSERVATIVE      1
#define STRATEGY_RECURSIVE         2
#define STRATEGY_CONCLUSIVE        3

//added by yanlin
/* argument register width used*/
#define  TEMPORARY                //To Handle Temp

//#define unopt

#define  STRATEGY_WIDTH  

//output statistics on different cases
#define STATISTICS

//For case that default size of source operand is 64-bit
#define SixToThree               //Identify and Handle Lea
/*for case: in this case, it should be in categroy read63
mov %rcx, 0x08(%rsp)
......
mov 0x08(%rsp), %rax
lea (%rax,1,), eax
*/
#define secondLea

#define six2three_policy

#define CHECK_XOR           
#define xor_policy           //Handle NUll
#define constant_policy      //Handel Pointer and Imm

#define Variadic_Over

//#define SUPPORT_GCC

//#define WRAPPER_OPT
/* policy for variadic function idenfication, used*/ 
#define STRATEGY_accurate_variadic        //Handle Nor2var in Clang

//#define  CHECK_DCALL

//#define FOLLOW_DIRECT_CALL


/*for argument width, when the argument is constant 
  stored in .rodata and .bss section, used*/
#define PARSE_DATA_SECTION   

/*if the predecessor of an indirect call can be another indirect, use 
the basic blocks between these two calls to get the argument count.
not used */
//#define BETWEEN_CALL

/* for argument width, when the argument is constant, we should
    promote the register width not used */
#define IMMEDIATE_VALUE
//end of yanlin   


#define ALLOW_UNINITIALIZED_READ

// TODO this is really TOO conservative...
//#define CONSERVATIVE_CALLSITE

/* Possible options for conservative strategy */
#define STRATEGY_CON_OPT_EXPECT_2ND_RETVAL  0x01
#define STRATEGY_CON_OPT_2                  0x02

/* Possible options for recursive strategy */
#define STRATEGY_REC_OPT_1            0x01
#define STRATEGY_REC_OPT_2            0x02
#define STRATEGY_REC_OPT_3            0x04


/* Strategy type and option */
//#define STRATEGY_TYPE       STRATEGY_RECURSIVE
//the default strategy used in this implementation
#define STRATEGY_TYPE       STRATEGY_CONCLUSIVE
#define STRATEGY_OPTIONS    STRATEGY_CON_OPT_EXPECT_2ND_RETVAL




#ifdef DEBUG
#define  dprintf(...) fprintf(stderr, __VA_ARGS__)
#else
#define dprintf(...) void()
#endif

#ifdef DDEBUG
#define ddprintf(...) fprintf(stderr, __VA_ARGS__)
#else
#define ddprintf(...) void()
#endif

struct OperandType : public InstructionAPI::Visitor {
    virtual void visit(InstructionAPI::BinaryFunction *) { binaryFunction = true; }
    virtual void visit(InstructionAPI::Dereference *)    { dereference    = true; } 
    virtual void visit(InstructionAPI::Immediate *)      { immediate      = true; }
    virtual void visit(InstructionAPI::RegisterAST* )    { registerAST    = true; }
    OperandType(): binaryFunction(false), 
                      dereference(false), 
                        immediate(false),
                      registerAST(false) {};
    bool binaryFunction,
         dereference,
         immediate,
         registerAST;
};


/*********************************** ARMS REGISTER ***********************************/

string ArmsRegister::getStateName(StateType state) {
    switch(state) {
        case IA64_READ:  return "read ";
        case IA64_WRITE: return "write";
        case IA64_RW:    return "r/w  ";
        case IA64_CLEAR: return "clear";
        default: {
                     dprintf("WTF: %d\n", state);
                     return "unkown";
                 };
    }
}

void ArmsRegister::setDeref(ArmsBasicBlock *block, unsigned long offset) {
    deref_block_list[block][offset] = true;
}

#ifdef STRATEGY_WIDTH
/* added by yanlin to set width of an argument register*/
void ArmsRegister::setWidth_read(ArmsBasicBlock *block, unsigned long offset, int width)
{
    if (width == 0)
        width = 16;
    block_list_width_read[block][offset] = width;
}

void ArmsRegister::setWidth_write(ArmsBasicBlock *block, unsigned long offset, int width)
{
    block_list_width_write[block][offset] = width;
}

int ArmsRegister::getwidth_write(ArmsBasicBlock *block, unsigned long offset)
{
    return block_list_width_write[block][offset];
}

int ArmsRegister::getWidth_offset(ArmsBasicBlock *block, unsigned long offset)
{
    return block_list_width_read[block][offset];
}

//test
void ArmsRegister::insn_test(ArmsBasicBlock *block, unsigned long offset, std::string ins_str)
{
   ins_list[block][offset] = ins_str; 

}

#ifdef TEMPORARY
void ArmsRegister::offsetToins(ArmsBasicBlock *block, unsigned long offset, Instruction::Ptr iptr)
{
   offset2ins[block][offset] = iptr;

}
#endif



int ArmsRegister::data_instruction_test(ArmsBasicBlock *block)
{
    int width = 0;
    std::size_t found_data_ins = 0;
    std::string str2 = "movs";
    std::string str1 = "cdq";
    std::string str3 = "sh";
    std::string str4 = "not";
    std::string str5 = "bswap";
    std::string str6 = "and";
    std::string str7 = "or";
    std::string str8 = "inc";
    std::string str9 = "dec";
    std::string str10 = "sa";
    std::string str11 = "movz";
    std::string str12 = "add";
    std::string str13 = "sub";
    std::string str14 = "mul";
    std::string str15 = "mova";
    if (block_list_width_write.count(block) != 1) return width;
    for (register_it_width it  = block_list_width_write[block].begin(); 
                       it != block_list_width_write[block].end(); 
                       it++)
    {
        unsigned long insn_offset = it->first;  /* instruction offset */
        width = it->second;
        std::string ins_str = ins_list[block][insn_offset];
        if (width == 8){
            std::size_t found = ins_str.find(str2);
            if (found != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find movs instruction %s\n",ins_str.c_str());
            }
            std::size_t found_neg = ins_str.find(str1);
            if (found_neg != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find cdq instruction %s\n",ins_str.c_str());
            }
            std::size_t found_sh = ins_str.find(str3);
            if (found_sh != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find sh instruction %s\n",ins_str.c_str());
            }
            std::size_t found_not = ins_str.find(str4);
            if (found_not != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find not instruction %s\n",ins_str.c_str());
            }
            std::size_t found_swap = ins_str.find(str5);
            if (found_swap != std::string::npos)
            {
                found_data_ins = 1;

                ddprintf("find bswap instruction %s\n",ins_str.c_str());
            }
            
            std::size_t found_and = ins_str.find(str6);
            if (found_and != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find and instruction %s\n",ins_str.c_str());
            }
            
            std::size_t found_or = ins_str.find(str7);
            if (found_or != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find or instruction %s\n",ins_str.c_str());
            }
            std::size_t found_inc = ins_str.find(str8);
            if (found_inc != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find inc instruction %s\n",ins_str.c_str());
            }
            std::size_t found_dec = ins_str.find(str9);
            if (found_dec != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find dec instruction %s\n",ins_str.c_str());
            }

            std::size_t found_sa = ins_str.find(str10);
            if (found_sa != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find sa instruction %s\n",ins_str.c_str());
            }
            
            std::size_t found_movz = ins_str.find(str11);
            if (found_movz != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find movz instruction %s\n",ins_str.c_str());
            }
            std::size_t found_add = ins_str.find(str12);
            if (found_add != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find add instruction %s\n",ins_str.c_str());
            }

            std::size_t found_sub = ins_str.find(str13);
            if (found_sub != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find sub instruction %s\n",ins_str.c_str());
            }
            std::size_t found_mul = ins_str.find(str14);
            if (found_mul != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find mul instruction %s\n",ins_str.c_str());
            }

            std::size_t found_mova = ins_str.find(str15);
            if (found_mova != std::string::npos)
            {
                found_data_ins = 1;
                ddprintf("find mova instruction %s\n",ins_str.c_str());
            }
        }
    }
    return found_data_ins;
}
//end of test

/* added by yanlin. return the width for this register in one block for a callee*/
int ArmsRegister::getWidth_callsite(ArmsBasicBlock *block)
{
    int width = 0;
    int final_width = 0;
    int final_ins  = 0;

    

    if (block_list_width_write.count(block) != 1) return width;

    for (register_it_width it  = block_list_width_write[block].begin(); 
                       it != block_list_width_write[block].end(); 
                       it++)
    {
        unsigned long insn_offset = it->first;  /* instruction offset */
        width = it->second;

        if ( width >= final_width  )
        {
            if (width != 0)
                final_width = width;
        }
        else if (width == 4)
        {
            final_width = width;
        }
        /*if (block_list[block][insn_offset] == IA64_CLEAR ) 
        {
            //dprintf("find the first state\n");
            break;
        }*/
    }
    return final_width;
}

bool ArmsRegister::isWrite(ArmsBasicBlock *block)
{
    int width;
    int final_width = 9;

    for (register_it_width it  = block_list_width_read[block].begin(); 
                       it != block_list_width_read[block].end(); 
                       it++)
    {

        unsigned long insn_offset = it->first;  // instruction offset 
        width = it->second;

        //dprintf("width for each offset %d\n", width);
        //if (block_list[block][insn_offset] == IA64_READ)
        
        if (width == 0)
        {
            width = 9;
        }
        
        if ( width <= final_width)
        {
            final_width = width;
        }

        if (width == 17 && final_width != 9) 
        {
            return true;
        }
    }
    return false;

}


/* added by yanlin. return the width for this register in one block for an indirect call*/
int ArmsRegister::getWidth_callee(ArmsBasicBlock *block)
{
    int width;
    int final_width = 9;

    if (block_list_width_read.count(block) != 1) return 0;


    for (register_it_width it  = block_list_width_read[block].begin(); 
                       it != block_list_width_read[block].end(); 
                       it++)
    {

        unsigned long insn_offset = it->first;  // instruction offset 
        width = it->second;

        //dprintf("width for each offset %d\n", width);
        //if (block_list[block][insn_offset] == IA64_READ)
        
        if (width == 0)
        {
            width = 9;
        }
        
        if ( width <= final_width)
        {
            final_width = width;
        }

        if (width < final_width && final_width != 9)
        {
            dprintf("find smalller width in one block %lx,%d,%d\n",block->get_start_address(),width,final_width);
        }
    
        
        if (width == 17) 
        {
            dprintf("find write operation %lx\n",block->get_start_address());
            return final_width;
        }
    }
    dprintf("width for each block %d\n", final_width);
    return final_width;
}

/* added by yanlin. return the width for this register in a number of blocks */
int ArmsRegister::getWidth_callsite(std::vector<ArmsBasicBlock *> blocks)
{
    int width = 0; /* register is untouched by default */
    int final_width = 0;
    //test
    int found_data_ins;
    int final_found_data_ins = 0;
    int found = 0;
    int overwrite_data_ins = 0;
    //end of test
    StateType reg_state = IA64_CLEAR;
    /* call getwidth() for each block until the register is no longer clear */
    for (std::vector<ArmsBasicBlock *>::iterator it  = blocks.begin();
                                                 it != blocks.end();
                                                 it++) {
        //dprintf("backward analysis***\n");
        width = getWidth_callsite(*it);
        reg_state = getState(*it);

        //start of test
        found_data_ins = data_instruction_test(*it);

        if (found_data_ins && final_found_data_ins == 0)
        {
            final_found_data_ins = found_data_ins;
        }

        if (final_found_data_ins && found_data_ins == 0 && width != 0)
        {
            overwrite_data_ins = 1;
            ddprintf("overwrite on argument register \n");
        }
        //end of test

        if ( width >= final_width && width != 0)
        {
            final_width = width;
        }
        /* stop once the first state change was observed */
        //if (reg_state != IA64_CLEAR) break;
    }
    //test
    if (!overwrite_data_ins && final_found_data_ins)
    {
        ddprintf("find data instruction\n");
    }
    //end of test
    return final_width;
}

int ArmsRegister::getWidth_callee(std::vector<ArmsBasicBlock *> blocks)
{
    int width; /* register is untouched by default */
    int final_width = 9;
    StateType reg_state = IA64_CLEAR;
    int first_flag = 1;
    /* call getwidth() for each block until the register is no longer clear */
    for (std::vector<ArmsBasicBlock *>::iterator it  = blocks.begin();
                                                 it != blocks.end();
                                                 it++) {
        width = getWidth_callee(*it);
        reg_state = getState(*it);
        //dprintf("width for each offset %d\n", width);
        if (reg_state == IA64_READ)
        {
            if ( width == 0)
            {
                width = 9;
            }
            if ( width <= final_width)
            {
                final_width = width;
            }
        }
        /* stop once the first state change was observed */
        //if (reg_state == IA64_WRITE) break;
    }
   //dprintf("width for callee %d\n", final_width);
    return final_width;
}
#endif
//end of yanlin

#ifdef SixToThree

int ArmsRegister::write32bit(Instruction::Ptr iptr)
{
    std::set<RegisterAST::Ptr> register_set;

    iptr->getWriteSet(register_set);

    for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                              it != register_set.end(); 
                                              it++) {
        RegisterAST::Ptr reg = *it;
        MachRegister cur = reg->getID();
        int width = cur.size();

        if (width == 4)
        {
            return 1;
        }

    }
    return 0;
}

int ArmsRegister::getSixtoThree(ArmsBasicBlock *block)
{
   int  first = 1;
   int width;
   for (register_it_width it  = block_list_width_read[block].begin(); 
                       it != block_list_width_read[block].end(); 
                       it++)
    {

        unsigned long insn_offset = it->first;  /* instruction offset */
        width = it->second; 
        std::string ins_str = ins_list[block][insn_offset];
        
        std::size_t found = ins_str.find("lea");


       // printf("checking\n");
        {
            if ( width == 8)
            {
                if (found != std::string::npos)
                {
                    //if ()
                    //printf("lea ins\n");
                    {
                        //printf("lea 64 to 32\n");
                        return 1;
                    }
                }
            }
            else if (width != 0 )
            {
                first = 0;
                return 0;
            }
        }
    }
    return 0;
}
#endif 



void ArmsRegister::setState(ArmsBasicBlock *block, unsigned long offset, StateType state) {
//  dprintf("setState(%p, %p, %d) (this: %p)\n", block, (void *) offset, state, this);

    /* An instruction can read and write to the same register. */ 
    if ((block_list[block][offset] == IA64_READ  && state == IA64_WRITE) || 
        (block_list[block][offset] == IA64_WRITE && state == IA64_READ)) {
        block_list[block][offset] = IA64_RW;
    } else {
        block_list[block][offset] = state;
    }


}
void ArmsRegister::setRead(ArmsBasicBlock *block, unsigned long offset) {
    setState(block, offset, IA64_READ);
}
void ArmsRegister::setWrite(ArmsBasicBlock *block, unsigned long offset) {
    setState(block, offset, IA64_WRITE);
}

#ifdef TEMPORARY
RegisterAST::Ptr ArmsRegister::readARGtoARG(ArmsBasicBlock *bb,Instruction::Ptr iptr,unsigned int offset)
{
    std::vector<Operand> operands;
		
	iptr->getOperands(operands);

    std::string ins_str = iptr->format(0).c_str();

    std::size_t found = ins_str.find("mov");

    //dprintf("instruction info %s,lx\n",iptr->format(0).c_str(),offset);
    if (found != std::string::npos)
    {   
        ddprintf("find mov instruction %s,%lx\n",iptr->format(0).c_str(),offset);    
        if (operands.size() == 2)
        {
            Operand operand = operands[1];

            OperandType operandType;
            operand.getValue()->apply(&operandType);

            std::string str =  operand.format(Arch_x86_64).c_str();

            if (str.size() <= 3 && !operandType.immediate)
            {
        
                if (getState(bb,offset) == IA64_RW || getState(bb,offset) == IA64_WRITE)
                {
                    ddprintf("argtoarg instruction %s,%lx\n",iptr->format(0).c_str(),offset);
                    std::set<RegisterAST::Ptr> register_set;

                    iptr->getReadSet(register_set);
                    for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                                        it != register_set.end(); 
                                                        it++) {
                            RegisterAST::Ptr reg = *it;
                            //int  reg_value = reg->getID().val();

                            return reg;
                    }

                }
            }


        }
    }
    return NULL;

    /*
    StateType reg_state;
    for (state_it_type it  = block_list[block].begin();
                       it != block_list[block].end();
                       it++) {
        unsigned long insn_offset = it->first;
        reg_state = it->second;

        if (reg_state == IA64_WRITE || reg_state == IA64_RW)
        {
            Instruction::Ptr iptr = offset2ins[block][insn_offset];

            std::vector<Operand> operands;
		
		
		    iptr->getOperands(operands);
            
            if (operands.size() == 2)
            {

                std::set<RegisterAST::Ptr> register_set;

                iptr->getReadSet(register_set);

                for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                                it != register_set.end(); 
                                                it++) {
                    RegisterAST::Ptr reg = *it;
                    //int  reg_value = reg->getID().val();

                    return reg;

                
                }
            }
            return NULL;



        }
    }

    return NULL;*/
}
#endif 

bool ArmsRegister::writtenInBlock(ArmsBasicBlock *block) {
    StateType reg_state;

    for (state_it_type it  = block_list[block].begin();
                       it != block_list[block].end();
                       it++) {
        unsigned long insn_offset = it->first;
        reg_state = it->second;

        if (reg_state == IA64_WRITE || reg_state == IA64_RW) return true;
    }

    return false;
}

bool ArmsRegister::writtenInBlocks(std::set<ArmsBasicBlock *> blocks) {

    for (std::set<ArmsBasicBlock *>::iterator it  = blocks.begin();
                                              it != blocks.end();
                                              it++) {
        ArmsBasicBlock *block = *it;
        if (writtenInBlock(block)) return true;
    }

    return false;
}

bool ArmsRegister::writtenLastInBlock(ArmsBasicBlock *block) {
    StateType reg_state;

    for (state_rit_type rit  = block_list[block].rbegin();
                        rit != block_list[block].rend();
                        rit++) {
        unsigned long insn_offset = rit->first;
        reg_state = rit->second;

        if (reg_state == IA64_WRITE) return true;
        if (reg_state == IA64_RW)    return true;
        if (reg_state == IA64_CLEAR) continue;
        return false;
    }

    return false;
}

StateType ArmsRegister::getLastState(ArmsBasicBlock *block) {
    StateType reg_state = IA64_CLEAR;

    for (state_rit_type rit  = block_list[block].rbegin();
                        rit != block_list[block].rend();
                        rit++) {
        unsigned long insn_offset = rit->first;
        reg_state = rit->second;

        if (reg_state != IA64_CLEAR) break;
    }

    return reg_state;
}

/* Returns the RW state for this register in a specific block. This assumes
 * that the instructions for this block were parsed in consecutive order. */
StateType ArmsRegister::getState(ArmsBasicBlock *block) {
    StateType reg_state = IA64_CLEAR; /* register is untouched by default */

    if (block_list.count(block) != 1) return reg_state;

    /* loop over all recorded states for this block */
    for (state_it_type it  = block_list[block].begin(); 
                       it != block_list[block].end(); 
                       it++) {
        unsigned long insn_offset = it->first;  /* instruction offset */
        reg_state = it->second;

        /* stop once the first state change was observed */
        if (reg_state != IA64_CLEAR) break;
    }

    return reg_state;
}

bool ArmsRegister::getDeref(ArmsBasicBlock *block) {
    bool deref = false;

    if (deref_block_list.count(block) != 1) return deref;

    for (deref_it_type it = deref_block_list[block].begin();
                       it != deref_block_list[block].end();
                       it++) {
        unsigned long insn_offset = it->first;
        deref = it->second;

        if (deref) break;
    }

    return deref;
}


StateType ArmsRegister::getState(ArmsBasicBlock *block, unsigned long offset) {
    if (block_list.count(block) != 1) return IA64_CLEAR;
    if (block_list[block].count(offset) != 1) return IA64_CLEAR;
    return block_list[block][offset];
}

/* Returns the RW state for this register in a number of blocks */
StateType ArmsRegister::getState(std::vector<ArmsBasicBlock *> blocks) {
    StateType reg_state = IA64_CLEAR; /* register is untouched by default */

    /* call getState() for each block until the register is no longer clear */
    for (std::vector<ArmsBasicBlock *>::iterator it  = blocks.begin();
                                                 it != blocks.end();
                                                 it++) {
        reg_state = getState(*it);

        /* stop once the first state change was observed */
        if (reg_state != IA64_CLEAR) break;
    }
    return reg_state;
}


ArmsBasicBlock * ArmsRegister::getBB(std::vector<ArmsBasicBlock *> blocks, StateType state) {
    for (std::vector<ArmsBasicBlock *>::iterator it  = blocks.begin();
                                                 it != blocks.end();
                                                 it++) {
        if (getState(*it) == state) return *it;
    }
    return NULL;
}

unsigned long ArmsRegister::getOffset(ArmsBasicBlock *block, StateType state) {
    for (state_it_type it  = block_list[block].begin(); 
                       it != block_list[block].end(); 
                       it++) {
        unsigned long insn_offset = it->first;
        int reg_state = it->second;

        if (reg_state == state) return insn_offset;
    }
    return 0;
}




/*********************************** ARMS LIVENESS ***********************************/

// static
string ArmsLiveness::get_register_name(int reg) {
    switch(reg) {
        case IA64_RDI: return "RDI";
        case IA64_RSI: return "RSI";
        case IA64_RDX: return "RDX";
        case IA64_RCX: return "RCX";
        case IA64_R8:  return "R8 ";
        case IA64_R9:  return "R9 ";
        case IA64_RSP: return "RSP";
        case IA64_RBP: return "RBP";
        case IA64_RAX: return "RAX";
        case IA64_R10: return "R10";
        //added by yanlin
        case IA64_R11: return "R11";
        case IA64_R12: return "R12";
        case IA64_R13: return "R13";
        case IA64_R14: return "R14";
        case IA64_R15: return "R15";
        case IA64_RBX: return "RBX";
        default: return "unknown";
    }
}

// static
// revised by yanlin

int ArmsLiveness::parse_functions(ArmsFunction *f, void *arg, std::vector<std::vector<unsigned long>> data_info) {
    ArmsLiveness *alive = (ArmsLiveness *) arg;
    
    return alive->parse_function(f,data_info);
}



int ArmsLiveness::getFirstReadArgRegister(ArmsBasicBlock *bb, unsigned long offset) {

    for (int i = 0; i < IA64_ARGS; i++) {
        if (rw_registers[i].getState(bb, offset) == IA64_READ)
            return i;
    }

    return IA64_ARGS;
}




bool ArmsLiveness::is_analyzed(ArmsBasicBlock *bb) {
    return analyzed_blocks.find(bb) != analyzed_blocks.end();
}

int get_reg_index(RegisterAST::Ptr reg) {
    int reg_value = reg->getID().val();
    int reg_class = reg->getID().regClass();
    
    //added by yanlin to get the width of a register
    MachRegister cur = reg->getID();
    int size = cur.size();
    ddprintf("register size            : %s->(%d): \n",  cur.name().c_str(), size);
    
    
    if (reg_class != x86::GPR) {
        /* not a GPR (could be a flag or RIP or ...) */
        return -1;
    }
    switch(reg_value & 0x000000ff ) {
        case 0: // RAX
            return IA64_RAX;
            break;
        case 1: // RCX
            return IA64_RCX;
            break;
        case 2: // RDX
            return IA64_RDX;
            break;
        case 3: // RBX
            return IA64_RBX;
            break;
        case 4: // RSP
            return IA64_RSP;
            break;
        case 5: // RBP
            return IA64_RBP;
            break;
        case 6: // RSI
            return IA64_RSI;
            break;
        case 7: // RDI
            return IA64_RDI;
            break;
        case 8: // R8
            return IA64_R8;
            break;
        case 9: // R9
            return IA64_R9;
            break;
        case 10: // R10
            return IA64_R10;
            break;
        case 11: // R11
            return IA64_R11;
            break;
        case 12: // R12
            return IA64_R12;
            break;
        case 13: // R13
            return IA64_R13;
            break;
        case 14: // R14
            return IA64_R14;
            break;
        case 15: // R15
            return IA64_R15;
            break;
        default: // anything else
            break;
    }
    return -1;
}

#ifdef PARSE_DATA_SECTION
int ArmsLiveness::isbbConstantArg(ArmsBasicBlock *bb, int i)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) return 0; // TODO

    std::vector<int> first;
    
    for ( int i = 0; i< IA64_REGS; i++)
    {
        first.push_back(1);
    }
    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                            it != insns.rend(); 
                                            it++) 
    {
        if (width_registers[i].getwidth_write(bb,it->first) == 4)
        {
            if (insn_constant[bb][it->first])
            {
                //printf("constant %lx,%lx\n",bb->get_start_address(),it->first);
                return insn_constant[bb][it->first];
            }
            else
                return 0;
        }
        
    }
    return 0;
}

int ArmsLiveness::isbbConstantArgFirst(ArmsBasicBlock *block, int t)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) block->get_parse_block();
    if (!pblock) 
    {
        ddprintf("cannot find this block %lx\n",block->get_start_address());
        return 0;
    } // TODO

    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);


    /*for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                            it != insns.rend(); 
                                            it++) {
    
    
    
    }*/

    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != --insns.end(); 
                                            it ++)
    {
        for (int j = 0 ; j < IA64_REGS; j++)
        {
            if (insn_constant[block][it->first])
            {
                auto nx = std::next(it, 1);
                if (width_registers[j].getWidth_offset(block,nx->first) == 4)
                {
                    
                    if (width_registers[t].getwidth_write(block,nx->first) == 4)
                    {                  
                        ddprintf("constant arg first %lx\n",it->first);
                        return insn_constant[block][it->first];
                    }
                
                }
            }
        }
        //return 0;
    }

    return 0;

    
}


#endif 


#ifdef CHECK_XOR



int ArmsLiveness::isBBXorFirst(ArmsBasicBlock *block, int t)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) block->get_parse_block();
    if (!pblock) 
    {
        ddprintf("cannot find this block %lx\n",block->get_start_address());
        return 0;
    } // TODO

    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);


    /*for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                            it != insns.rend(); 
                                            it++) {
    
    
    
    }*/

    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != --insns.end(); 
                                            it ++)
    {
        for (int j = 0 ; j < IA64_REGS; j++)
        {
            if (isXorIns(it->second,block,it->first,j))
            {
                auto nx = std::next(it, 1);
                if (width_registers[j].getWidth_offset(block,nx->first) == 4)
                {
                    if (width_registers[t].getwidth_write(block,nx->first) == 4)
                    {
                        return 1;
                    }
                
                }
            }
        }
        //return 0;
    }

    return 0;

    
}





int ArmsLiveness::isXorIns(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int i)
{
    std::string ins_str = iptr->format(0).c_str();

    std::size_t found = ins_str.find("xor");

    //dprintf("instruction info %s,lx\n",iptr->format(0).c_str(),offset);
    if (found != std::string::npos)

    {
        ddprintf("find xor instruction %s,%lx\n",iptr->format(0).c_str(),offset);
        if (width_registers[i].getwidth_write(bb,offset) == 4)
        {
            return i+1;
        }
    }
    return 0;
}


int ArmsLiveness::isBBXorIns(ArmsBasicBlock *bb, int i)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) 
    {
        ddprintf("cannot find this block %lx\n",bb->get_start_address());
        return 0;
    } // TODO

    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                            it != insns.rend(); 
                                            it++) {
            
            if (isXorIns(it->second, bb, it->first,i))
            {
                return 1;
            }
            else if (width_registers[i].getwidth_write(bb,it->first) == 8)
            {
                return 0;
            }
    }
    

    return 0;
}
#endif


#ifdef SixToThree
int ArmsLiveness::ispush(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int t)
{
    std::string ins_str = iptr->format(0).c_str();

    std::size_t found = ins_str.find("push");

    //dprintf("instruction info %s,lx\n",iptr->format(0).c_str(),offset);
    if (found != std::string::npos)

    {
        ddprintf("find push instruction %s,lx\n",iptr->format(0).c_str(),offset);
        if (width_registers[t].getWidth_offset(bb,offset) == 8)
        {
            return t+1;
        }
    }
    return 0;
}

int ArmsLiveness:: isBBpush(ArmsBasicBlock *bb, int i)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) 
    {
        ddprintf("cannot find this block %lx\n",bb->get_start_address());
        return 0;
    } // TODO

    std::vector<int> first;
    
    for ( int i = 0; i< IA64_REGS; i++)
    {
        first.push_back(1);
    }
    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != insns.end(); 
                                            it++)
    {
        if (ispush(it->second, bb,it->first,i) && first[i])
        {
            ddprintf("instruction push %s,%lx\n",(it->second)->format(0).c_str(),it->first);
            //read64to32[bb][i] = 1; 
            return 1;
        }
        else if (width_registers[i].getWidth_offset(bb,it->first) == 4)
        {
            //read64to32[bb][i] = 0;
            //first[i] = 0;
            return 0;
        }    
        else if (width_registers[i].getwidth_write(bb,it->first) != 0)
        {
            first[i] = 0;
        }
    }

    return 0;
}

int ArmsLiveness::isBBRead64To32(ArmsBasicBlock *bb, int i)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) 
    {
        ddprintf("cannot find this block %lx\n",bb->get_start_address());
        return 0;
    } // TODO

    std::vector<int> first;
    
    for ( int i = 0; i< IA64_REGS; i++)
    {
        first.push_back(1);
    }
    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    //for (int i = 0; i < IA64_ARGS; i++)
    {
        for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != insns.end(); 
                                            it++) {
            /* it->first:  offset
            * it->second: instruction */
            ddprintf("instruction in block %s,%lx\n",(it->second)->format(0).c_str(), it->first);
            //int result = isRead64To32(it->second, bb,it->first,i);
            {
                //if (width_registers[i].getWidth_offset(bb,it->first) == 8)
                {
                    if (isRead64To32(it->second, bb,it->first,i) && first[i])
                    {
                        ddprintf("instruction lea %s,%lx\n",(it->second)->format(0).c_str(),it->first);
                        //read64to32[bb][i] = 1; 
                        return 1;
                    }
                    else if (width_registers[i].getWidth_offset(bb,it->first) == 4)
                    {
                        //read64to32[bb][i] = 0;
                        //first[i] = 0;
                        return 0;
                    }    
                    else if (width_registers[i].getwidth_write(bb,it->first) != 0)
                    {
                        first[i] = 0;
                    }
                }
            
            }
        }
    }
    return 0;
}

int ArmsLiveness::isRead64To32(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int t)
{
    std::string ins_str = iptr->format(0).c_str();

    std::size_t found = ins_str.find("lea");

    //dprintf("instruction info %s,lx\n",iptr->format(0).c_str(),offset);
    if (found != std::string::npos)

    {
        ddprintf("find lea instruction %s,lx\n",iptr->format(0).c_str(),offset);
        if (width_registers[t].getWidth_offset(bb,offset) == 8)
        {
            
            for (int i = 0 ;i < IA64_REGS; i++)
            {
                if (width_registers[i].getwidth_write(bb,offset) == 4)
                {
                    //read64to32[bb][offset] = 1;
                    return t+1;
                }
            }
            
        }
    }
    return 0;
}

int ArmsLiveness::isBBRead32To64(ArmsBasicBlock *bb, int i)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) return 0; // TODO

    std::vector<int> first;
    
    for ( int i = 0; i< IA64_REGS; i++)
    {
        first.push_back(1);
    }
    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    
    for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                            it != insns.rend(); 
                                            it++) 
    {
        /* it->first:  offset
        * it->second: instruction */
        
        if (width_registers[i].getwidth_write(bb,it->first) != 0)
        {
            if (isRead32To64(it->second, bb,it->first,i))
            {
                //printf("instruction %s\n",(it->second)->format(0).c_str());
                //read64to32[bb][i] = 1; 
                return 1;
            } 
            else
                return 0;
        }
    }
    return 0;

}

int ArmsLiveness::isBBRead16To32(ArmsBasicBlock *bb, int i)
{
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) return 0; // TODO

    std::vector<int> first;
    
    for ( int i = 0; i< IA64_REGS; i++)
    {
        first.push_back(1);
    }
    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    
    for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                            it != insns.rend(); 
                                            it++) 
    {
        /* it->first:  offset
        * it->second: instruction */
        
        if (width_registers[i].getwidth_write(bb,it->first) != 0)
        {
            if (isRead16To32(it->second, bb,it->first,i))
            {
                //printf("instruction %s\n",(it->second)->format(0).c_str());
                //read64to32[bb][i] = 1; 
                return 1;
            } 
            else
                return 0;
        }
    }
    return 0;

}


int ArmsLiveness::isRead16To32(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int i)
{
    for (int j = 0 ;j < IA64_REGS; j++)
    {
        if (width_registers[j].getWidth_offset(bb,offset) < 4 && width_registers[j].getWidth_offset(bb,offset)> 0)
        {
            
            if (width_registers[i].getwidth_write(bb,offset) == 4)
            {
                read32to64[bb][offset] = 1;
                return i+1;
            }
            
        }
    }
}

int ArmsLiveness::isRead32To64(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int i)
{
    std::string ins_str = iptr->format(0).c_str();

    
    for (int j = 0 ;j < IA64_REGS; j++)
    {
        if (width_registers[j].getWidth_offset(bb,offset) < 8 && width_registers[j].getWidth_offset(bb,offset)>=4)
        {
           
            if (width_registers[i].getwidth_write(bb,offset) == 8)
            {
                read32to64[bb][offset] = 1;
                return i+1;
            }
            
        }
    }

    return 0;
}
#endif

#ifdef PARSE_DATA_SECTION
void ArmsLiveness::parse_register(Instruction::Ptr iptr, std::vector<std::vector<unsigned long>> data_info,
                        RegisterAST::Ptr reg, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state)
#else
void ArmsLiveness::parse_register(RegisterAST::Ptr reg, 
                                  ArmsBasicBlock *bb, unsigned long offset, StateType state) 
#endif
{
    
    int reg_index = get_reg_index(reg);
    #ifdef STRATEGY_WIDTH
    MachRegister cur = reg->getID();
    int width = cur.size();
    #endif
    if (reg_index < 0) return;
    
    dprintf("              : (%d): %s -> %s\n", reg_index, 
                         get_register_name(reg_index).c_str(), 
                    ArmsRegister::getStateName(state).c_str());
    rw_registers[reg_index].setState(bb, offset, state);
    #ifdef TEMPORARY
    rw_registers[reg_index].offsetToins(bb,offset,iptr);
    #endif
    
    #ifdef STRATEGY_WIDTH
    std::string ins_str = iptr->format(0).c_str();
    std::size_t found = ins_str.find("xor");

    if (state == IA64_READ && found == std::string::npos)
        width_registers[reg_index].setWidth_read(bb, offset, width);
    
    else
    {
        width_registers[reg_index].setWidth_read(bb, offset, 17);
    }
    
    /*else if (found != std::string::npos)
        width_registers[reg_index].setWidth_read(bb, offset, 17);
    
    else if (width_registers[reg_index].getWidth_callee(bb) == 17)
        width_registers[reg_index].setWidth_read(bb, offset, 17);*/
    
    //if (rw_registers[reg_index].getState(bb) == IA64_READ && state == IA64_WRITE)
        //width_registers[reg_index].setWidth_read(bb, offset, 17);
    
    //if (rw_registers[reg_index].getState(bb) == IA64_WRITE && state == IA64_READ)
       // width_registers[reg_index].setWidth_read(bb, offset, 17);

    if (state == IA64_WRITE)
    {

        #ifdef PARSE_DATA_SECTION
        //(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int i)
        //if (isXorIns(iptr, bb, offset,reg_index))
            //width = 8;
        int t = isConstantArg(iptr, data_info);
        /*t: 1 for pointer in .data, rodata, and text section
             2 for immediate value
        */
        //if (t)
        {
            insn_constant[bb][offset] = t;
            ddprintf("operand points to data section %s\n",iptr->format(0).c_str());
            //if (t)
                //width = 8;
        }
        //added by yanlin, test
        std::string ins_str = iptr->format(0).c_str();
        width_registers[reg_index].insn_test(bb,offset,ins_str);
        
        //end of test 
        #endif

        
        //obtain argument register width that written
        width_registers[reg_index].setWidth_write(bb, offset, width);
        width_registers[reg_index].setWidth_read(bb, offset, 17);
        
    }
    #endif
    
}
//revised by yanlin
#ifdef PARSE_DATA_SECTION
void ArmsLiveness::parse_register_set(Instruction::Ptr iptr, std::vector<std::vector<unsigned long>> data_info,
                        std::set<RegisterAST::Ptr> register_set, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state) 
#else
void ArmsLiveness::parse_register_set(std::set<RegisterAST::Ptr> register_set, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state) 
#endif
{
 
    for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                              it != register_set.end(); 
                                              it++) {
        RegisterAST::Ptr reg = *it;
        int  reg_value = reg->getID().val();
        #ifdef PARSE_DATA_SECTION
        parse_register(iptr, data_info, reg, bb, offset, state);
        #else
        parse_register(reg, bb, offset, state);
        #endif
    }
}

bool isNop(Instruction::Ptr iptr) {
    if (iptr->getOperation().getID() == e_nop) return true;
    return false;
}

bool isNop(ArmsBasicBlock *bb) {
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);
    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                          it != insns.end(); 
                                          it++) {
        /* it->first:  offset
         * it->second: instruction */
        if (!isNop(it->second)) return false;
    }

    return true;
}

#ifdef PARSE_DATA_SECTION
void ArmsLiveness::parse_instruction(Instruction::Ptr iptr,
                                     ArmsBasicBlock *bb, unsigned long offset,
                                     std::vector<std::vector<unsigned long>> data_info) 
#else
void ArmsLiveness::parse_instruction(Instruction::Ptr iptr,
                                     ArmsBasicBlock *bb, unsigned long offset) 
#endif
{

    if (!iptr->isLegalInsn()) {
        dprintf("      %p: [ILLEGAL INSTRUCTION]\n", (void *) offset);
        bb->set_disas_err((void*) offset);
        return;
    }
    ddprintf("      %p: %s\n", (void *) offset, iptr->format(0).c_str());

    
    RegisterAST::Ptr reg = is_dereference(iptr);
    if (reg != NULL) {
        int reg_index = get_reg_index(reg);
        if (reg_index >= 0) {
            
            ddprintf("setting deref\n");
            rw_registers[reg_index].setDeref(bb, offset);
        }
    }


    ins_length[offset] = iptr->size();

    if (iptr->size() == 2 && iptr->rawByte(0) == 0xF3 && iptr->rawByte(1) == 0x90) {
        dprintf("                PAUSE\n");
        return;
    }
    if (iptr->size() == 2 && iptr->rawByte(0) == 0x0F && iptr->rawByte(1) == 0xA2) {
        dprintf("                CPUID\n");
        RegisterAST::Ptr eax(new RegisterAST(x86::eax)); // TODO
        RegisterAST::Ptr ebx(new RegisterAST(x86::ebx));
        RegisterAST::Ptr ecx(new RegisterAST(x86::ecx));
        RegisterAST::Ptr edx(new RegisterAST(x86::edx));
        #ifdef PARSE_DATA_SECTION
        parse_register(iptr, data_info, eax, bb, offset, IA64_WRITE);
        parse_register(iptr, data_info,ebx, bb, offset, IA64_WRITE);
        parse_register(iptr, data_info,ecx, bb, offset, IA64_WRITE);
        parse_register(iptr, data_info,edx, bb, offset, IA64_WRITE);
        #else
        parse_register(eax, bb, offset, IA64_WRITE);
        parse_register(ebx, bb, offset, IA64_WRITE);
        parse_register(ecx, bb, offset, IA64_WRITE);
        parse_register(edx, bb, offset, IA64_WRITE);
        #endif
        return;
    }
    /* TODO: for us, syscalls are not indirect calls. we should modify the arms
     * interface so that it does not add those edges in the first place */
    if (iptr->size() == 2 && iptr->rawByte(0) == 0x0F && iptr->rawByte(1) == 0x05) {
        dprintf("                SYSCALL\n");
        bb->set_syscall();
    }
/* TODO:
    if (iptr->size() == 2 && iptr->rawByte(0) == 0x0f && iptr->rawByte(1) == 0x0b) {
        dprintf("                UD2\n");
    }
 */
        //revised by yanlin
    if (iptr->getOperation().getID() == e_xor or iptr->getOperation().getID() == e_sbb)
    {
		ddprintf("                XOR or sbb instruction\n");
		std::vector<Operand> operands;
		std::set<RegisterAST::Ptr> writtenSet;
		
		iptr->getOperands(operands);
		
		operands[0].getWriteSet(writtenSet);
		#ifdef PARSE_DATA_SECTION
        parse_register_set(iptr, data_info, writtenSet, bb, offset, IA64_WRITE);
        #else
		parse_register_set(writtenSet, bb, offset, IA64_WRITE);
        #endif
		writtenSet.clear();
		
	}              

    std::set<RegisterAST::Ptr> register_set;

    if (!isNop(iptr)) iptr->getReadSet(register_set);
    #ifdef PARSE_DATA_SECTION
    parse_register_set(iptr, data_info,register_set, bb, offset, IA64_READ);
    #else
    parse_register_set(register_set, bb, offset, IA64_READ);
    #endif
    register_set.clear();



    if (!isNop(iptr)) iptr->getWriteSet(register_set);
    #ifdef secondLea
    //offsetToins(bb,offset,iptr);
    //offset2reg[offset] = register_set;
    //offset2insstr[offset] = iptr->format(0).c_str();
    #endif


    #ifdef PARSE_DATA_SECTION
    parse_register_set(iptr, data_info,register_set, bb, offset, IA64_WRITE);
    #else
    parse_register_set(register_set, bb, offset, IA64_WRITE);
    #endif
    register_set.clear();

    /*#ifdef PARSE_DATA_SECTION
    if (!isNop(iptr))
    {
        if (isConstantArg(iptr,data_info))
        {
            dprintf("operand points to data section %s\n",iptr->format(0).c_str());
        }
    }
    #endif*/
    
    //revised by yanlin
    if (iptr->getOperation().getID() == e_xor or iptr->getOperation().getID() == e_sbb)
    {
		ddprintf("                XOR or sbb instruction\n");
		std::vector<Operand> operands;
		std::set<RegisterAST::Ptr> writtenSet;
		
		iptr->getOperands(operands);
		
		operands[0].getWriteSet(writtenSet);
		#ifdef PARSE_DATA_SECTION
        parse_register_set(iptr, data_info, writtenSet, bb, offset, IA64_WRITE);
        #else
		parse_register_set(writtenSet, bb, offset, IA64_WRITE);
        #endif
		writtenSet.clear();
		
	}

    /*if (isRead64To32(iptr,bb,offset))
    {
        dprintf("read 64 bit and write 32 bit %s\n",iptr->format(0).c_str());
    }*/

    /*if (isRead32To64(iptr,bb,offset))
    {
        dprintf("read 32 bit and write 64 bit %s\n",iptr->format(0).c_str());
    }*/



}

#ifdef PARSE_DATA_SECTION
void ArmsLiveness::parse_block(ArmsFunction *f, ArmsBasicBlock *bb,std::vector<std::vector<unsigned long>> data_info)
#else
void ArmsLiveness::parse_block(ArmsFunction *f, ArmsBasicBlock *bb) 
#endif
{
    /* Analyze blocks only once */
    if (is_analyzed(bb)) {
        dprintf("O NO\n");
        return;
    }

    dprintf("  - Analyzing block %p - %p\n", (void *)bb->get_start_address(),
                                           (void *)bb->get_last_insn_address());

    /* The ArmsBasicBlock stores a pointer to either a ParseAPI::Block or a
     * BPatchBasicBlock. We currently only support the first. */
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) return; // TODO

    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    //added by yanlin
    bool is_ret = false;
    bool is_nop = false;
    Instruction::Ptr instr;
    std::set<ArmsBasicBlock*> *bbs = f->get_basic_blocks();
    #ifdef PARSE_DATA_SECTION
    bool is_indirect = false;
    if (bb->outgoing_edge_count() >= 1)
        is_indirect = bb->get_outgoing_edge(0)->is_indirect_call();
    #endif
    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                          it != insns.end(); 
                                          it++) {
        /* it->first:  offset
         * it->second: instruction */
        /*#ifdef secondLea
        offset2ins2[it->first] = it->second;
        #endif*/
        #ifdef PARSE_DATA_SECTION
        if (is_indirect)
        {
            if(isConstantArg(it->second, data_info))
                ddprintf("find operand in indirect call\n");
        }
        parse_instruction(it->second, bb, it->first,data_info);
        #else
        parse_instruction(it->second, bb, it->first);
        #endif
        instr = it->second;
        std::string ins_str = (it->second)->format(0).c_str();
        if (ins_str.find("nop") != std::string::npos)
        {
            is_nop = true;
            ddprintf("****nop edge %lx\n",bb->get_last_insn_address());
        }
        
    }

    //added by yanlin
    std::string ins_str = (instr)->format(0).c_str();
    if (ins_str.find("ret") != std::string::npos)
    {
        is_ret = true;
        ddprintf("****return edge %lx\n",bb->get_last_insn_address());
    }
    //end

    ddprintf("    Block summary:\n");
    for (int i = 0; i < IA64_REGS; i++) {
        ddprintf("      %s: %s\n",            get_register_name(i).c_str(), 
                               ArmsRegister::getStateName(rw_registers[i].getState(bb)).c_str() );
        
        /*#ifdef STRATEGY_WIDTH
        dprintf("      %s: %d\n",            get_register_name(i).c_str(), 
                               width_registers[i].getWidth_callee(bb));
        dprintf("      %s: %d\n",            get_register_name(i).c_str(), 
                               width_registers[i].getWidth_callsite(bb));
        #endif*/
    }
    
    

    analyzed_blocks.insert(bb);
    function_blocks[f].push_back(bb);

    /* Recursively analyze adjacent blocks by looping over the outgoing edges of
     * this block. */

    /* TODO The order of analyzing blocks is dictated by how we traverse the
     * CFG. This could have an impact on the read before write states, consider
     * code like:
     * 
     *      cmp rax, 0
     *      je foo
     *      mov rcx, 2
     * foo: mov r15, rcx
     *
     * In above example, depending on the order we traverse the blocks, we may
     * conclude that rcx is write before read (in case we do not follow the
     * conditional jump to label foo), or read before write (when we analyze the
     * code at label foo first).
     *
     * Analysis will have to tell whether this is a problem.
     */
    ddprintf("    > edges: %lu\n",bb->outgoing_edge_count());
    
    if (!is_ret){
    
        for(size_t i = 0; i < bb->outgoing_edge_count(); i++) {
            ArmsEdge *edge = bb->get_outgoing_edge(i);
            ArmsBasicBlock *next_bb;
    
            /* We do not want to leave the current function */
            if (edge->is_return()) {
                ddprintf("    > Not following return edge\n");
                continue;
            } else if (edge->is_direct_call()) {
                ddprintf("    > Not following direct call edge, looking at fallthrough bb instead\n");
                /* TODO: test whether a direct call is made to a function that exits
                * Maybe it easier to try to use the ARMS interface to get a hold on
                * all the basicblocks for a specific function, instead of doing all
                * the work again here... --> ARMS nor ParseAPI won't solve this :( */
                
                #ifdef FOLLOW_DIRECT_CALL
                if ( edge->target() != NULL &&
                    edge->target()->get_function() != NULL && 
                    !edge->target()->get_function()->is_plt()&& !(edge->target()->get_function()->get_name() == "_EXIT" ||
                    edge->target()->get_function()->get_name() == "_exit" || 
                    edge->target()->get_function()->get_name() == "die" ||
                    edge->target()->get_function()->get_name() == "__stack_chk_fail"||
                    edge->target()->get_function()->get_name().find("throw") != string::npos))
                {
                    ddprintf("find direct calls that call a function\n");
                    call_blocks[f].insert(bb);
                }
                #endif
                
                if (edge->target() != NULL &&
                    edge->target()->get_function() != NULL &&
                    (edge->target()->get_function()->get_name() == "_EXIT" ||
                    edge->target()->get_function()->get_name() == "_exit")) {
                    ddprintf("    > Call to _EXIT, not even looking at fallthrough bb\n");
                    continue;
                }
                //added by yanlin
                /*if (edge->target()->get_function()->is_plt())
                    next_bb = bb->get_fallthrough_bb();
                else
                    next_bb = edge->target();*/
                next_bb = bb->get_fallthrough_bb();
                #ifdef BETWEEN_CALL
                if (next_bb != NULL)
                    ret_blocks[f].insert(next_bb);
                #endif
                //#ifdef BETWEEN_CALL
                //if (next_bb != NULL)
                    //ret_blocks[f].insert(next_bb);
                //#endif
        
                
            } else if(edge->is_indirect_call()) {
                //dprintf("yanlin indirect branch");
                ddprintf("    > Not following indirect call edge, looking at fallthrough bb instead\n");
                next_bb = bb->get_fallthrough_bb();
                
                #ifdef BETWEEN_CALL
                if (next_bb != NULL)
                    ret_blocks[f].insert(next_bb);
                #endif
                

                /* This looks like a great place to perform the live analysis for
                * indirect callsites. However, if we need to implement our own
                * analysis algoritm here, we need to remember that not all basic
                * blocks of this function may be parsed yet. For this reason, we
                * do the icall analysis AFTER the entire function was analyzed.
                * 
                * To speed fix up a bit, we store this basicblock so we do not have
                * to go over all the blocks again.
                */
                icall_blocks[f].insert(bb);

            } else {
                ddprintf("    > Getting target of edge\n");
                next_bb = edge->target();
                //added by yanlin
                if (edge_type_is_indirect_jmp(edge->type()) && next_bb->is_entry_block())
                    continue;

                if (next_bb->is_entry_block() && !edge->is_interprocedural())
                {
                    next_bb = NULL;
                    continue;
                }
                if (is_nop) 
                {
                    ddprintf("nop fallthrough %lx\n",bb->get_last_insn_address());
                    if (next_bb->is_entry_block()){
                        next_bb = NULL;
                        ddprintf("next block is in another function %lx\n",bb->get_last_insn_address());
                        continue;
                    }
                }
                
                

                
                //if (next_bb != NULL)
                    //dprintf("next bb addr is %lx\n",next_bb->get_start_address());
            }

            if (next_bb == NULL) {
                ddprintf("    > next bb does not exist\n");
                continue;
            }

            if (edge->is_direct_call() && isNop(next_bb)) {
                ddprintf("    > fallthrough is nop while last edge was a direct call. Assuming non-returning\n");
                //continue;
            }

            if (edge->is_direct_call() && next_bb->is_entry_block()) {
                ddprintf("    > fallthrough is entry block while last edge was a direct call. Assuming non-returning\n");
                continue;
            }
            

            if (is_analyzed(next_bb)) {
                ddprintf("    > next bb is already analyzed\n");
                continue;
            }

            std::vector<ArmsFunction*> funcs = next_bb->get_functions();
            if (funcs.size() == 0) {
                ddprintf("    > next bb is not from any function\n");
                continue;
            }
            for (std::vector<ArmsFunction *>::iterator it  = funcs.begin();
                                                    it != funcs.end();
                                                    it++) {
                if (*it == f) {
                    goto function_found;
                }

            }
            ddprintf("    > next bb is from a different function:\n");
            for (std::vector<ArmsFunction *>::iterator it  = funcs.begin();
                                                    it != funcs.end();
                                                    it++) {
                ArmsFunction *fun = *it;
                ddprintf("      > %s\n", fun->get_name().c_str());
            }

            continue;

    function_found:
            #ifdef PARSE_DATA_SECTION
            this->parse_block(f, next_bb,data_info);
            #else
            this->parse_block(f, next_bb);
            #endif
        }
    }
}


int ArmsLiveness::parse_function(ArmsFunction *f, std::vector<std::vector<unsigned long>> data_info) {
    #ifdef FOLLOW_DIRECT_CALL
    all_functions[f->get_base_addr()] = f;
    #endif
    
    if(f->is_plt() || f->is_lib_dummy()) {
        ddprintf("* Skipping analysis of function %s\n", f->get_name().c_str());
        return 0;
    } 
    ddprintf("* Analyzing function %s\n", f->get_name().c_str());


    std::set<ArmsBasicBlock*> *bbs = f->get_basic_blocks();
    for (std::set<ArmsBasicBlock *>::iterator it  = bbs->begin();
                                              it != bbs->end();
                                              it++) {
        ArmsBasicBlock *b = *it;
        ddprintf("- basicblock %p - %p\n", (void *)b->get_start_address(),
                                          (void *)b->get_last_insn_address());
    }

    std::vector<ArmsBasicBlock*> entry_blocks;
    entry_blocks.assign(f->get_entry_points()->begin(), f->get_entry_points()->end());

    function_blocks[f].clear();
    icall_blocks[f].clear();

    //added by yanlin
    #ifdef FOLLOW_DIRECT_CALL
    call_blocks[f].clear();
    #endif

    /* Recursively analyze each block of the function starting from the entry blocks */
    while(entry_blocks.size() > 0) {
        ArmsBasicBlock *bb = entry_blocks.back();
        entry_blocks.pop_back();

        #ifdef PARSE_DATA_SECTION
        parse_block(f, bb,data_info);
        #else
        parse_block(f, bb);
        #endif
    }

    dprintf("    Function summary:\n");
    for (int i = 0; i < IA64_REGS; i++) {
        ddprintf("      %s: %s\n", get_register_name(i).c_str(), 
            ArmsRegister::getStateName(rw_registers[i].getState(function_blocks[f])).c_str() );

        #ifdef STRATEGY_WIDTH
         dprintf("      %s: %d\n", get_register_name(i).c_str(), 
            width_registers[i].getWidth_callee(function_blocks[f]) );
        #endif
    
    }


    return 0;
}


string ArmsLiveness::get_regstate_name(int i, ArmsFunction *f) {
    return ArmsRegister::getStateName(rw_registers[i].getState(function_blocks[f]));
}





/**** DETECTING VARIADIC FUNCTIONS ****/

bool ArmsLiveness::also_read(int k, ArmsBasicBlock *bb, int reg_index) {
    for (int i = k; i < IA64_ARGS; i++) {
        unsigned long offset = rw_registers[i].getReadOffset(bb);
        ddprintf("  [varargs.C4] State for %s at offset %lx (1st read of %s): %s\n", 
                get_register_name(reg_index).c_str(), offset, get_register_name(i).c_str(), 
                ArmsRegister::getStateName( rw_registers[reg_index].getState(bb,offset) ).c_str());
                
        if (rw_registers[reg_index].getState(bb,offset) != IA64_READ) {
            return false;
        }
    }
    return true;
}

// added by yanlin
#ifdef PARSE_DATA_SECTION
bool IsThisStringAHexNumber(std::string const &str)
{
    
    for (size_t i = 0, n = str.length(); i < n; ++i)
        if (!std::isxdigit(str[i]))
            return false;

    return true;
}
int ArmsLiveness::isConstantArg(Instruction::Ptr iptr, std::vector<std::vector<unsigned long>> data_info)
{
    std::vector<Operand> operands;
    iptr->getOperands(operands);

    if (operands.size() == 2)
    {
        Operand operand = operands[1];

        Expression::Ptr expr = operand.getValue();

        OperandType operandType;
        operand.getValue()->apply(&operandType);

        if (operandType.immediate)
        {
            std::string str =  operand.format(Arch_x86_64).c_str();
            ddprintf("*** operand %s\n",str.c_str());
            if (!IsThisStringAHexNumber(str))
                return 0;
            #ifdef IMMEDIATE_VALUE
            if (str.size() <= 8)
            {
                return 2;
            }
            #else
            if (str.size() < 6)
                return 2;
            if (str.size() > 8)
                return 0;
            

            unsigned long value = std::stol(str,nullptr,16);

            ddprintf("operand value %ld\n", value);

            std::vector<std::vector<unsigned long>>::iterator data_it;
            for (data_it = data_info.begin(); data_it!=data_info.end(); ++data_it)
            {
                std::vector<unsigned long> x = *data_it;
                
                ddprintf("data info %ld, %ld\n",x.front(),x.back());
                if ( value < x.back() && value >= x.front())
                {
                    ddprintf("yanlin find this constant\n");
                    return 1;
                }
                
            }
            return 2;
            #endif

        }

        
        
    }
    return 0;
}
#endif
//end of yanlin


//added by yanlin
/*
#ifdef FOLLOW_DIRECT_CALL
bool ArmsLiveness::directCall_follow_entry_blocks(std::set<ArmsBasicBlock *> *preceding_blocks, ArmsFunction *f, 
                                                  unsigned long dcall_addr)
{
    std::set<ArmsBasicBlock*>* entry_blocks = f->get_entry_points(); 

    for (std::set<ArmsBasicBlock *>::iterator it  = entry_blocks->begin();
                                              it != entry_blocks->end();
                                              it++){
        
        ArmsBasicBlock *entry_block = *it;
        if (preceding_blocks->count(entry_block))
        {
            dprintf("the proceeding of the direct call can be the entry block %lx\n",dcall_addr);
            return true;
        }
                                                
    }
    return false;
}

ArmsFunction * ArmsLiveness::find_function(address_t base_address){

	std::map<address_t, ArmsFunction *>::iterator it = all_functions.find(base_address);
	if (it == all_functions.end())
		return NULL;

	return it->second;
}
//static
int ArmsLiveness::parse_functions_second_time(ArmsFunction *f, void *arg) {
    ArmsLiveness *alive = (ArmsLiveness *) arg;
    return alive->entryToDirectCall(f);
}
//check whether a basic block can be accessed from the entry block of a function
int ArmsLiveness::entryToDirectCall(ArmsFunction *f)
{
    int i = 0;
    dprintf("call_blocks size %d\n",call_blocks.size());
    for (std::set<ArmsBasicBlock *>::iterator it  = call_blocks[f].begin();
                                              it != call_blocks[f].end();
                                              it++, i++) {
        ArmsBasicBlock *block = *it;
        unsigned long dcall_addr = block->get_last_insn_address();
        dprintf("\n%s() got dcall in basic block: %p\n", f->get_name().c_str(), (void*)block->get_start_address());


         
        ParseAPI::Block *pblock = (ParseAPI::Block *) block->get_parse_block();
        Instruction::Ptr iptr = pblock->getInsn( dcall_addr );

        dprintf("***              direct call instruction at: %p - %s\n", (void *)dcall_addr, iptr->format(0).c_str());


        

        std::set<ArmsBasicBlock *> preceding_blocks;
        block->get_preceding_bbs(&preceding_blocks, f->get_basic_blocks());
        preceding_blocks.insert(block);

        std::set<ArmsBasicBlock *>::iterator iter;
        for(iter = preceding_blocks.begin(); iter != preceding_blocks.end(); iter++) {
            ArmsBasicBlock *bb = *iter;
            dprintf("preceding block: %p - %p\n", (void *) bb->get_start_address(), (void *) bb->get_last_insn_address()); 
        } 

       

        bool follow_entry = directCall_follow_entry_blocks(&preceding_blocks, f, dcall_addr);
        
        if (follow_entry && preceding_blocks.size() == 1 ) 
        {
            dprintf("a function argument is redirect to the dcall!\n");
            
        }
    }
    return 0;
}
#endif*/


//whether an instruction read the stack
bool ArmsLiveness::read_stack(ArmsBasicBlock *bb, int reg_index, unsigned long offset)
{
    if (rw_registers[reg_index].getState(bb,offset) != IA64_READ) {
        return false;
    }
    return true;
}

//get the offset according to the given string
int ArmsLiveness::get_offset(std::string ins_str)
{
    printf("string %s\n",ins_str.c_str());
    std::string delimiter = "+";
    std::string delimiter_s = "]";
    std::size_t index1 = ins_str.find(delimiter);
    std::size_t index2 = ins_str.find(delimiter_s);
    int len = index2-index1-1;
    std::string offset_str = ins_str.substr(index1+1,len);
    if (offset_str.size() > 8)
        offset_str = offset_str.substr(len-8,8);
    ddprintf("instruction write to stack %s\n", offset_str.c_str());

    std::stringstream ss;
    ss << std::hex << offset_str;
    unsigned int offset;
    ss >> offset;
    ddprintf("offset is %d\n", static_cast<int>(offset));
    return static_cast<int>(offset);

}

//variadic parameters moved to continous stack address
int ArmsLiveness::VarConsecutive(ArmsBasicBlock *bb, int m,int begin,int last_stack_offset, ParseAPI::Block::Insns insns)
{
    int i;
    ParseAPI::Block::Insns::iterator it;
    for( i = begin; i >=m; i--)
    {
        unsigned long offset = rw_registers[i].getReadOffset(bb);
        int reg_width = width_registers[i].getWidth_offset(bb, offset);

        if (!read_stack(bb, IA64_RSP,offset) && !read_stack(bb, IA64_RBP,offset))
        {
            return i;
        }
        
        it = insns.find(offset);
        if (it != insns.end())
        {
            std::string ins_str = (it->second)->format(0).c_str();
            int stack_offset = get_offset(ins_str);
            if (!(last_stack_offset == stack_offset + reg_width || last_stack_offset == stack_offset - reg_width))
            {
                ddprintf("find non-consecutive address\n");
                return i;
            }
            last_stack_offset = stack_offset;
        }
    }
    return i;
}

#ifdef STRATEGY_accurate_variadic 
//whether all argument registers are moved to consecutive stack addresses
bool ArmsLiveness::allConsecutive(ArmsBasicBlock *bb, int m,int begin,int last_stack_offset, ParseAPI::Block::Insns insns)
{
    int i;
    ParseAPI::Block::Insns::iterator it;
    for( i = begin; i >=m; i--)
    {
        unsigned long offset = rw_registers[i].getReadOffset(bb);
        int reg_width = width_registers[i].getWidth_offset(bb, offset);

        if (!read_stack(bb, IA64_RSP,offset) && !read_stack(bb, IA64_RBP,offset))
        {
            return false;
        }
        
        it = insns.find(offset);
        if (it != insns.end())
        {
            std::string ins_str = (it->second)->format(0).c_str();
            int stack_offset = get_offset(ins_str);
            if (!(last_stack_offset == stack_offset + reg_width || last_stack_offset == stack_offset - reg_width))
            {
                ddprintf("find non-consecutive address\n");
                return false;
            }
            last_stack_offset = stack_offset;
        }
    }
    return true;
}

//whether the stack address that used to store the argument register is reused somewhere else
bool ArmsLiveness::reuseOperand(ArmsFunction *f, std::string op, ArmsBasicBlock* last_bb)
{
    std::set<ArmsBasicBlock*> *bbs = f->get_basic_blocks();
    ParseAPI::Block::Insns insns;
    ParseAPI::Block *pblock;
    
    Expression::Ptr expr;

    for (std::set<ArmsBasicBlock *>::iterator it  = bbs->begin();
                                              it != bbs->end();
                                              it++) 
    {
        ArmsBasicBlock *bb = *it;
        if ( bb != last_bb)
        {
            pblock= (ParseAPI::Block *) bb->get_parse_block();
            if (!pblock) 
            { 
                ddprintf("Null pblock");
                return 0; // TODO
            }
            pblock->getInsns(insns);
            for (ParseAPI::Block::Insns::iterator it_ins  = insns.begin(); 
                                                it_ins != insns.end(); 
                                                it_ins++) {
                
                std::vector<Operand> operands;
                (it_ins->second)->getOperands(operands);
                std:string ins_str = (it_ins->second)->format(0).c_str();

                //operand = (it_ins->second)->getOperand(1);
                ddprintf("iterating ins %s\n",(it_ins->second)->format(0).c_str());
                //dprintf("Operand size %d\n",operands.size());
                if (operands.size() > 1)
                {
                    std::string delimiter = ",";
                    std::size_t index = ins_str.find(delimiter);

                    int len = ins_str.size() - index-1;

                    std::string operand1 = ins_str.substr(index+2,len);

                    
                    //dprintf("operand %s %d %d\n",operand1.c_str(), operand1.size(),op.size());

                    if (operand1 == op)
                    {
                        ddprintf("find operand %s\n",operand1.c_str());
                        return true;
                    }
                    
                }
            }
        }
        
    }
    return false;

}

//get the number of arguments that are moved to the consecutive address of the stack
int ArmsLiveness::consecutiveAddress(ArmsBasicBlock *bb, int m, int n, int last_stack_offset)
{
    ddprintf("consecutiveAddress Enter %d\n", m);
    int i;
    int k = m;
    // Parse the instructions of this basic block
    ParseAPI::Block::Insns insns;
    ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) 
    { 
        ddprintf("Null pblock");
        return 0; // TODO
    }
    pblock->getInsns(insns);
    ParseAPI::Block::Insns::iterator it;

    for( i = n - 1; i >=m; i--)
    {
        unsigned long offset = rw_registers[i].getReadOffset(bb);
        int reg_width = width_registers[i].getWidth_offset(bb, offset);
        ddprintf("Register width %d\n", reg_width);

        if ( reg_width != 8)
        {
            /*int j = i-1;
            it = insns.find(offset);
            if (it != insns.end())
            {
                std::string ins_str_i = (it->second)->format(0).c_str();
                int stack_offset_i = get_offset(ins_str_i);
                if ( m == 0){
                    if (allConsecutive(bb,m,j,stack_offset_i,insns))
                    {
                        k = 0;
                    }
                    else{
                        k = i+1;
                    }
                }
                else
                    k = i+1;
            }*/
            k = i+1;
            break;
        }
        
       if (!read_stack(bb, IA64_RSP,offset) && !read_stack(bb, IA64_RBP,offset))
        {
            ddprintf("It didn't read the stack");
            k = i+1;
            break;
        }

        it = insns.find(offset);
        if (it != insns.end())
        {
            std::string ins_str = (it->second)->format(0).c_str();
            ddprintf("instruction write to stack %s\n", (it->second)->format(0).c_str());
            int stack_offset = get_offset(ins_str);
            if (!((last_stack_offset == stack_offset + reg_width) || (last_stack_offset == stack_offset - reg_width)))
            {
                k = i+1;
                break;
            }
            last_stack_offset = stack_offset;

        }
        
        /*for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != insns.end(); 
                                            it++) {
            if ( it->first == offset)
            {
                //std::set<Expression::Ptr> memAccessors;
                //(*it->second)->getMemoryWriteOperands(memAccessors);
                std::string ins_str = (it->second)->format(0).c_str();
                //dprintf("instruction write to stack %s\n", (it->second)->format(0).c_str());
                int stack_offset = get_offset(ins_str);
                if (!(last_stack_offset == stack_offset + reg_width || last_stack_offset == stack_offset - reg_width))
                {
                    k = i+1;
                    return k;
                }
                last_stack_offset = stack_offset;
                break;
            }
        }*/
    }
    
    return k;
}
#endif
//end of yanlin

#ifdef secondLea

bool ArmsLiveness::useinLea(ArmsFunction *f, std::string op, ArmsBasicBlock* last_bb)
{
    std::set<ArmsBasicBlock*> *bbs = f->get_basic_blocks();
    ParseAPI::Block::Insns insns;
    ParseAPI::Block *pblock;
    
    Expression::Ptr expr;
    int find_lea = 0;
    int previous_offset, previous_size;
    for (std::set<ArmsBasicBlock *>::iterator it  = bbs->begin();
                                              it != bbs->end();
                                              it++) 
    {
        ArmsBasicBlock *bb = *it;
        if ( bb != last_bb)
        {
            pblock= (ParseAPI::Block *) bb->get_parse_block();
            if (!pblock) 
            { 
                ddprintf("Null pblock");
                return 0; // TODO
            }
            pblock->getInsns(insns);
            for (ParseAPI::Block::Insns::iterator it_ins  = insns.begin(); 
                                                it_ins != insns.end(); 
                                                it_ins++) {
                
                std::vector<Operand> operands;
                (it_ins->second)->getOperands(operands);
                std:string ins_str = (it_ins->second)->format(0).c_str();

                //operand = (it_ins->second)->getOperand(1);
                //ddprintf("iterating ins %s\n",(it_ins->second)->format(0).c_str());
                //dprintf("Operand size %d\n",operands.size());
                if (operands.size() > 1)
                {
                    std::string delimiter = ",";
                    std::size_t index = ins_str.find(delimiter);

                    int len = ins_str.size() - index-1;

                    std::string operand1 = ins_str.substr(index+2,len);

                    
                    //dprintf("operand %s  %s %d %d\n",operand1.c_str(), op.c_str(), operand1.size(),op.size());

                    if (find_lea)
                    {
                        //ParseAPI::Block::Insns::iterator temp = it_ins;
                        ParseAPI::Block::Insns::iterator next_it_insn = it_ins;
                        int offset = next_it_insn->first;
                        //dprintf("next ins offset %lx\n",offset);
                        if (previous_offset+previous_size != offset)
                            return false;
                        //dprintf("next ins is at %lx\n",offset);
                        std::string next_ins_str =(next_it_insn->second)->format(0).c_str();
                        std::size_t found = next_ins_str.find("lea");
                        find_lea = 0;
                        if (found != std::string::npos)
                        {
                            //dprintf("find lea %s\n",next_ins_str.c_str());
                            //parse_instruction(it->second, bb, it->first);
                            Instruction::Ptr iptr = next_it_insn->second;
                            if (!iptr->isLegalInsn()) {
                                dprintf("      %p: [ILLEGAL INSTRUCTION]\n", (void *) offset);
                                bb->set_disas_err((void*) offset);
                                return false;
                            }
                           // dprintf("      %p: %s\n", (void *) offset, iptr->format(0).c_str());
                            std::set<RegisterAST::Ptr> register_set;

                            if (!isNop(iptr)) iptr->getWriteSet(register_set);

                            for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                              it != register_set.end(); 
                                                                    it++) {
                                RegisterAST::Ptr reg = *it;
                                int  reg_value = reg->getID().val();

                                int reg_index = get_reg_index(reg);
                                MachRegister cur = reg->getID();
                                int width = cur.size();
                                if (width == 4)
                                    return true;
                               
                            }
                            register_set.clear();                                           
                            
                        }
                        return false;
                    }

                    else if (operand1 == op)
                    {
                        //dprintf("find operand %s\n",operand1.c_str());
                        previous_offset = it_ins->first;
                        previous_size = ins_length[previous_offset];
                        std::set<RegisterAST::Ptr> register_set_pre;
                    
                        Instruction::Ptr iptr = it_ins->second;
                        if (!isNop(iptr)) iptr->getWriteSet(register_set_pre);
                        for (std::set<RegisterAST::Ptr>::iterator it  = register_set_pre.begin(); 
                                              it != register_set_pre.end(); 
                                                                    it++) {
                                RegisterAST::Ptr reg = *it;
                                int  reg_value = reg->getID().val();

                                int reg_index = get_reg_index(reg);
                                MachRegister cur = reg->getID();
                                int width = cur.size();
                                if (width == 8)
                                {
                                    find_lea = 1;
                                    break;
                                }
                        }

                        //find_lea = 1;
                        //dprintf("previous ins offset %lx\n",previous_offset);
                        /*int offset = previous_offset + previous_size;
                        dprintf("next ins offset %lx\n",offset);
                        //Instruction::Ptr iptr = offset2ins2[offset];
                        std::string next_ins_str = offset2insstr[offset];;
                        //find_lea = 1;
                        std::size_t found = next_ins_str.find("lea");
                        find_lea = 0;
                        if (found != std::string::npos)
                        {
                            dprintf("find lea %s\n",next_ins_str.c_str());
                            //parse_instruction(it->second, bb, it->first);
                            //Instruction::Ptr iptr = next_it_insn->second;

                            dprintf("      %p: %s\n", (void *) offset, next_ins_str.c_str());
                            std::set<RegisterAST::Ptr> register_set;

                            //if (!isNop(iptr)) iptr->getWriteSet(register_set);
                            register_set = offset2reg[offset];

                            for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                              it != register_set.end(); 
                                                                    it++) {
                                RegisterAST::Ptr reg = *it;
                                int  reg_value = reg->getID().val();

                                int reg_index = get_reg_index(reg);
                                MachRegister cur = reg->getID();
                                int width = cur.size();
                                if (width == 4)
                                    return true;
                               
                            }
                                                                        
                            register_set.clear();
                        }
                        return false;*/
                        
                    }
                    
                }
            }
        }
        
    }
    return false;

}

/*void ArmsLiveness::offsetToins(ArmsBasicBlock *block, unsigned long offset, Instruction::Ptr iptr)
{
   offset2ins[block][offset] = iptr;

}*/

int ArmsLiveness::is_secondlea(ArmsFunction *f)
{
    // for this case, the read of the arguments will be in the entry basic block
    dprintf("check is secondlea function %s\n",f->get_name().c_str());
    std::vector<ArmsBasicBlock *> blocks;
    for (std::vector<ArmsBasicBlock *>::iterator it  = function_blocks[f].begin();
                                                 it != function_blocks[f].end();
                                                 it++) {
        ArmsBasicBlock *first_bb = *it;
        blocks.push_back(first_bb);
        /*if (bb->outgoing_contains_inter())*/
        
        int n = 0;
        for (int i = IA64_LAST_ARG; i >= 0; i--)
        {
             //dprintf("processing %d \n",i);
            if (rw_registers[i].isRead(blocks))
            {
                //dprintf("find reading \n");
                n = i;
                break;
            }
        }

        //dprintf("n is %d \n",n);
        if (n == 0) return 0; 


        ParseAPI::Block *pblock = (ParseAPI::Block *) first_bb->get_parse_block();
        if (!pblock) 
        { 
            //dprintf("Null pblock");
            return 0; // TODO
        }
        ParseAPI::Block::Insns insns;
        pblock->getInsns(insns);

        for (int i = n; i >= 0; i--) 
        {
            unsigned long offset = rw_registers[i].getReadOffset(first_bb);
            if (!read_stack(first_bb, IA64_RSP,offset) && !read_stack(first_bb, IA64_RBP,offset))
                continue;
            
            for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                        it != insns.end(); 
                                        it++) {
                if ( it->first == offset)
                {
                    std::string ins_str = (it->second)->format(0).c_str();
                    std::string delimiter_r = ",";
                    std::string space_r = " ";
                    std::size_t index_d_r = ins_str.find(delimiter_r);
                    int len_r = index_d_r;
                    std::string left_str_r = ins_str.substr(0,len_r);
                    std::size_t index_s_r = left_str_r.find(space_r);
                    int len_f_r = index_d_r - index_s_r-1;
                    std::string op_r = left_str_r.substr(index_s_r+1,len_f_r);

                    

                    //std::set<RegisterAST::Ptr> register_set;
                    
                    //Instruction::Ptr iptr = next_it_insn->second;
                    //if (!isNop(iptr)) iptr->getWriteSet(register_set);
                   

                    //dprintf("argument op may used for lea %s %s\n",f->get_name().c_str(), op_r.c_str());
                    if (useinLea(f, op_r, first_bb))
                    {   dprintf("offset is %lx\n",offset);
                        dprintf("argument op may used for lea %s %s\n",f->get_name().c_str(), op_r.c_str());
                        return (i+1);
                    }

                   continue;
                }
            }
        }
        
        /*for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != insns.end(); 
                                            it++)
        {
            
            for (int i = n; i >= 0; i--) 
            {
              //ddprintf("check argumet reading %d \n",i);
              //StateType state = rw_registers[i].getState(first_bb);

                //if (state == IA64_READ)
                {
                    //ddprintf("find argumet reading %d \n",i);
                    int width = width_registers[i].getWidth_callee(first_bb);
                    if (width != 8)
                        continue;
                    
                    //ddprintf("width is 8 \n");
                    int offset = it->first;
                    //ddprintf("offset is %lx\n",offset);
                    std::string ins_str = (it->second)->format(0).c_str();
                    if (!read_stack(first_bb, IA64_RSP,offset) && !read_stack(first_bb, IA64_RBP,offset))
                        continue;
                    
                    std::string delimiter_r = ",";
                    std::string space_r = " ";
                    std::size_t index_d_r = ins_str.find(delimiter_r);
                    int len_r = index_d_r;
                    std::string left_str_r = ins_str.substr(0,len_r);
                    std::size_t index_s_r = left_str_r.find(space_r);
                    int len_f_r = index_d_r - index_s_r-1;
                    std::string op_r = left_str_r.substr(index_s_r+1,len_f_r);
                   

                    dprintf("argument op may used for lea %s %s\n",f->get_name().c_str(), op_r.c_str());
                    if (useinLea(f, op_r, first_bb))
                    {   dprintf("offset is %lx\n",offset);
                        dprintf("argument op may used for lea %s %s\n",f->get_name().c_str(), op_r.c_str());
                        return (i+1);
                    }

                   continue;
                }
            }
            
            
        
        }*/
        return 0;
    
    }
    

}
#endif

/* This function can safely return 0 to indicate the function is not-variadic:
 * variadic functions always expect at least one argument. */
int ArmsLiveness::is_variadic(ArmsFunction *f) {
    ddprintf("check function %s\n",f->get_name().c_str());
    int i;

    /* Variadic functions do not necessarily read all argument registers: a
     * function may overwrite a non-varargs parameter without reading it first,
     * for example. However, it seems to be the case that for any optimization
     * level, the compiler always generates code that stores the registers that
     * hold varargs (the ...) onto the stack. In addition, this always seems to
     * happen in the same order (vaarg 1 before vaarg 2 before vaarg 3 ...) and
     * also always within the same basic block.
     * We identify four conditions:
     *  1. The last N argument registers are read before write for this function
     *  2. This happens in the same basic block.
     *  3. This happens in a specific order.
     *  4. They are written to the stack.
     * and a possible 5th condition:
     *  5. 1-4 happens before the first call instruction of a function. 
     * (6. Must happen within the first 3 basic blocks)
     * If all these conditions are met, we conclude that the function is
     * variadic and expects at least 6 - N arguments.
     */
    
    
    /* CONDITION 5:
     * Make sure that there are no call instructions before the affected basic
     * block. Since a called function may overwrite some of the parameter
     * registers, the varargs must have been stored before the call is made.
     * We enforce this by minimzing the number of basic blocks that can be analyzed.
     */
    std::vector<ArmsBasicBlock *> blocks;
    for (std::vector<ArmsBasicBlock *>::iterator it  = function_blocks[f].begin();
                                                 it != function_blocks[f].end();
                                                 it++) {
        ArmsBasicBlock *bb = *it;
        blocks.push_back(bb);
        if (bb->outgoing_contains_inter()) break;
    }


    /* CONDITION 1:
     * Get the number of arugment registers that were read before write */
    int n = 0;
    #ifdef SUPPORT_GCC
    for (i = IA64_LAST_ARG; i >= n; i--)
    {
        if (rw_registers[i].isRead(blocks))
        {
            n = i;
            break;
        }
    }

    if (n == 0) return 0;

    int k = 0;
    ArmsBasicBlock *last_bb = rw_registers[n].getReadBB(blocks);

    for (i = n; i >= 0; i--) {
        ArmsBasicBlock *bb = rw_registers[i].getReadBB(blocks);
        ddprintf("  [varargs.C2] %d: %s - %p\n", i, get_register_name(i).c_str(), (void *)bb);

        if (last_bb != bb) {
            k = i+1;
            break;
        }
    }

    int m = k;

    
    unsigned long last_seen_offset = rw_registers[IA64_LAST_ARG].getReadOffset(last_bb);
    
    if (!read_stack(last_bb, IA64_RSP,last_seen_offset) && !read_stack(last_bb, IA64_RBP,last_seen_offset))
        return 0;
    
    
    int last_regWidth = width_registers[n].getWidth_offset(last_bb, last_seen_offset);
    
    if (last_regWidth != 8)
        return 0;

    ParseAPI::Block *pblock = (ParseAPI::Block *) last_bb->get_parse_block();
    if (!pblock) 
    { 
        ddprintf("Null pblock");
        return 0; // TODO
    }

    //the number of arguments moved to the stack
    for (i = n-1; i >= m; i--)
    {
        unsigned long offset = rw_registers[i].getReadOffset(last_bb);
        if (!read_stack(last_bb, IA64_RSP,offset) && !read_stack(last_bb, IA64_RBP,offset))
        {
            m = i +1;
            break;
        }
    }

    // Parse the instructions of this basic block
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                        it != insns.end(); 
                                        it++) {
        if ( it->first == last_seen_offset)
        {
            //std::set<Expression::Ptr> memAccessors;
            //(*it->second)->getMemoryWriteOperands(memAccessors);
            std::string ins_str = (it->second)->format(0).c_str();
            //dprintf("instruction write to stack %s\n", (it->second)->format(0).c_str());
            int last_stack_offset = get_offset(ins_str);
            if (m == 0)
            {
                ddprintf("m==0 %s\n",f->get_name().c_str());
                if (allConsecutive(last_bb,m,IA64_LAST_ARG-1,last_stack_offset,insns))
                {
                    ddprintf("move all arguments to the stack\n");
                    return 0;
                }
                
            }
            else
            {
                std::string delimiter = ",";
                std::string space = " ";
                std::size_t index_d = ins_str.find(delimiter);
                int len = index_d;
                std::string left_str = ins_str.substr(0,len);
                std::size_t index_s = left_str.find(space);
                int len_f = index_d - index_s-1;
                std::string op = left_str.substr(index_s+1,len_f);
                ddprintf("last argument op %s %s\n",f->get_name().c_str(), op.c_str());
                
                if (reuseOperand(f, op, last_bb))
                {
                    return 0;
                }
                
            }

            m = consecutiveAddress(last_bb, k, IA64_LAST_ARG,last_stack_offset);
            //break;
            goto return_label;
        }
    }
    
    //for gcc the varadic parameter order is %rdx, %rcx, %r8 and %r9
    last_seen_offset = rw_registers[n].getReadOffset(last_bb);
    for (ParseAPI::Block::Insns::reverse_iterator rit  = insns.rbegin(); 
                                        rit != insns.rend(); 
                                        rit++){
        if ( rit->first == last_seen_offset)
        {
            std::string ins_str_gcc = (rit->second)->format(0).c_str(); 
            ddprintf("instruction string %s\n",ins_str_gcc.c_str());
            if (ins_str_gcc.find('[') != std::string::npos)
            {
                int last_stack_offset_r = get_offset(ins_str_gcc);
                if (m == 0)
                {
                    ddprintf("m==0 %s\n",f->get_name().c_str());
                    if (allConsecutive(last_bb,m,IA64_LAST_ARG-1,last_stack_offset_r,insns))
                    {
                        ddprintf("move all arguments to the stack\n");
                        return 0;
                    }
                }
                else
                {
                    std::string delimiter_r = ",";
                    std::string space_r = " ";
                    std::size_t index_d_r = ins_str_gcc.find(delimiter_r);
                    int len_r = index_d_r;
                    std::string left_str_r = ins_str_gcc.substr(0,len_r);
                    std::size_t index_s_r = left_str_r.find(space_r);
                    int len_f_r = index_d_r - index_s_r-1;
                    std::string op_r = left_str_r.substr(index_s_r+1,len_f_r);
                    ddprintf("last argument op %s %s\n",f->get_name().c_str(), op_r.c_str());
                    
                    if (reuseOperand(f, op_r, last_bb))
                    {
                        return 0;
                    }
                    
                }
            
                m = consecutiveAddress(last_bb, k, n, last_stack_offset_r);
                break;
            }
        } 
    }
    
    #else
    ddprintf("  [varargs.C1] Searching for last n arguments that are read before write... %s\n",f->get_name().c_str());
    for (i = IA64_LAST_ARG; i >= n; i--) {
        ddprintf("  [varargs.C1] %d: %s - %s\n", i, get_register_name(i   ).c_str(), 
                                                    get_regstate_name(i, f).c_str());
        if (!rw_registers[i].isRead(blocks)) {
            n = i + 1;
            break;
        }
    }
    //printf("number of registers read before write is %s %d\n",f->get_name().c_str(), n);
    /* If zero argument registers were found (i.e., R9 was not read before
     * write), we conclude that this function is not variadic. It could still be
     * variadic of course, if it has more than 6 constant arguments. */
    
    
    
    
    if (i == IA64_LAST_ARG) return 0;
    
    /* At this moment, we know that argument registers n, n+1, ..., 6 are
     * all read before write. */
    
    /* CONDITION 2:
     * Get the number of read before write arguments that had their first read
     * instruction in the same basic block. */
    int k = n;
    ArmsBasicBlock *last_bb = rw_registers[IA64_LAST_ARG].getReadBB(blocks);
    ddprintf("  [varargs.C2] Matching basic blocks against %p...\n", (void *)last_bb);
    for (i = IA64_LAST_ARG; i >= k; i--) {
        ArmsBasicBlock *bb = rw_registers[i].getReadBB(blocks);
        ddprintf("  [varargs.C2] %d: %s - %p\n", i, get_register_name(i).c_str(), (void *)bb);

        if (last_bb != bb) {
            k = i + 1;
            break;
        }
    }

	//printf("number of registers condition 2 is %s %d\n",f->get_name().c_str(), k);
    /* At this moment, we know that argument registers k, k+1, ..., 6 are all
     * read before write within the same basic block. */


    /* TODO. condition 3 must be strong: it must even be the next instruction.
     * */

    /* CONDITION 3:
     * Get the number of read before write arguments for which their read
     * instructions (that rely in the same basic block) occurred in consecutive
     * order. This could either be Rx, Ry, ..., R8, R9 for gcc or R9, R8, ...
     * Ry, Rx for clang. */
    int m = k;

    unsigned long last_seen_offset = rw_registers[IA64_LAST_ARG].getReadOffset(last_bb);
    
    //int r = m;
    //added by yanlin
    #ifdef STRATEGY_accurate_variadic
    if (!read_stack(last_bb, IA64_RSP,last_seen_offset) && !read_stack(last_bb, IA64_RBP,last_seen_offset))
        return 0;
    
    int last_regWidth = width_registers[IA64_LAST_ARG].getWidth_offset(last_bb, last_seen_offset);
    
    if (last_regWidth != 8)
        return 0;

    ParseAPI::Block *pblock = (ParseAPI::Block *) last_bb->get_parse_block();
    if (!pblock) 
    { 
        ddprintf("Null pblock");
        return 0; // TODO
    }

    //the number of arguments moved to the stack
    for (i = IA64_LAST_ARG-1; i >= m; i--)
    {
        unsigned long offset = rw_registers[i].getReadOffset(last_bb);
        if (!read_stack(last_bb, IA64_RSP,offset) && !read_stack(last_bb, IA64_RBP,offset))
        {
            m = i +1;
            break;
        }
    }

    // Parse the instructions of this basic block
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);

    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                        it != insns.end(); 
                                        it++) {
        if ( it->first == last_seen_offset)
        {
            //std::set<Expression::Ptr> memAccessors;
            //(*it->second)->getMemoryWriteOperands(memAccessors);
            std::string ins_str = (it->second)->format(0).c_str();
            //dprintf("instruction write to stack %s\n", (it->second)->format(0).c_str());
            int last_stack_offset = get_offset(ins_str);
            /*if (m == 0)
            {
                ddprintf("m==0 %s\n",f->get_name().c_str());
                if (allConsecutive(last_bb,m,IA64_LAST_ARG-1,last_stack_offset,insns))
                {
                    ddprintf("move all arguments to the stack\n");
                    return 0;
                }
            }
            else
            {
                
                std::string delimiter = ",";
                std::string space = " ";
                std::size_t index_d = ins_str.find(delimiter);
                int len = index_d;
                std::string left_str = ins_str.substr(0,len);
                std::size_t index_s = left_str.find(space);
                int len_f = index_d - index_s-1;
                std::string op = left_str.substr(index_s+1,len_f);
                ddprintf("last argument op %s %s\n",f->get_name().c_str(), op.c_str());
                if (reuseOperand(f, op, last_bb))
                {
                    return 0;
                }
               
            }*/

            m = consecutiveAddress(last_bb, k, IA64_LAST_ARG, last_stack_offset);
            break;
        }
    }

    //for gcc the varadic parameter order is %rdx, %rcx, %r8 and %r9
    
    /*for (ParseAPI::Block::Insns::reverse_iterator rit  = insns.rbegin(); 
                                        rit != insns.rend(); 
                                        rit++){
        if ( rit->first == last_seen_offset)
        {
            std::string ins_str_gcc = (rit->second)->format(0).c_str(); 
            int last_stack_offset_r = get_offset(ins_str_gcc);
            if (m == 0)
            {
                ddprintf("m==0 %s\n",f->get_name().c_str());
                if (allConsecutive(last_bb,m,IA64_LAST_ARG-1,last_stack_offset_r,insns))
                {
                    ddprintf("move all arguments to the stack\n");
                    return 0;
                }
            }
            else
            {
                std::string delimiter_r = ",";
                std::string space_r = " ";
                std::size_t index_d_r = ins_str_gcc.find(delimiter_r);
                int len_r = index_d_r;
                std::string left_str_r = ins_str_gcc.substr(0,len_r);
                std::size_t index_s_r = left_str_r.find(space_r);
                int len_f_r = index_d_r - index_s_r-1;
                std::string op_r = left_str_r.substr(index_s_r+1,len_f_r);
                ddprintf("last argument op %s %s\n",f->get_name().c_str(), op_r.c_str());
                if (reuseOperand(f, op_r, last_bb))
                {
                    return 0;
                }
            }
            m = consecutiveAddress(last_bb, k, IA64_LAST_ARG,last_stack_offset_r);
            break;
        } 
    } */
    
    //dprintf("yanlin debuging \n");
    
    #else
    ddprintf("  [varargs.C3] Comparing offsets...\n");
    for (i = IA64_LAST_ARG-1; i >= m; i--) {
        unsigned long offset = rw_registers[i].getReadOffset(last_bb);
#if 0
        ddprintf("  [varargs.C3] %d: %lx (read of %s) < %lx (read of %s)?\n", 
                i,           offset, get_register_name(i).c_str(), 
                   last_seen_offset, get_register_name(i+1).c_str());

        if (offset >= last_seen_offset) {
#else
        ddprintf("  [varargs.C3] %d: %lx (read of %s) > %lx (read of %s)?\n", 
                i,           offset, get_register_name(i).c_str(), 
                   last_seen_offset, get_register_name(i+1).c_str());

        if (offset != last_seen_offset + ins_length[offset]) {
#endif
            m = i + 1;
            break;
        }

        last_seen_offset = offset;
    }
    #ifdef Variadic_Over
    //added by yanlin, for program compiled by gcc
    last_seen_offset = rw_registers[IA64_LAST_ARG].getReadOffset(last_bb);
    m = k;
    ddprintf(" last_seen_offset [varargs.C3] %lx, %s\n", 
                   last_seen_offset,f->get_name().c_str());
    
    for (i = IA64_LAST_ARG-1; i >= k; i--)
    {
        unsigned long offset_gcc = rw_registers[i].getReadOffset(last_bb);
        ddprintf(" offset gcc [varargs.C3] %lx, %s\n", 
                   offset_gcc,f->get_name().c_str());
        if (last_seen_offset != offset_gcc + ins_length[offset_gcc])
        {
            ddprintf(" last_seen_offset [varargs.C3] %lx, %s\n", 
                   last_seen_offset,f->get_name().c_str());
            m = i +1;
            break;
        }

        last_seen_offset = offset_gcc;
    }

    if (m == 0)
        m = m +1;


    {
        ParseAPI::Block *pblock = (ParseAPI::Block *) last_bb->get_parse_block();
        ParseAPI::Block::Insns insns;
        pblock->getInsns(insns);
        last_seen_offset = rw_registers[IA64_LAST_ARG].getReadOffset(last_bb);
        for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                            it != insns.end(); 
                                            it++) {
            if ( it->first == last_seen_offset)
            {
                //std::set<Expression::Ptr> memAccessors;
                //(*it->second)->getMemoryWriteOperands(memAccessors);
                std::string ins_str = (it->second)->format(0).c_str();
                //dprintf("instruction write to stack %s\n", (it->second)->format(0).c_str());
                
                
                if (read_stack(last_bb, IA64_RSP,last_seen_offset) || read_stack(last_bb, IA64_RBP,last_seen_offset))
                {
                    int last_stack_offset = get_offset(ins_str);
                    
                    int t = VarConsecutive(last_bb,k,IA64_LAST_ARG-1,last_stack_offset,insns);
                        
                    
                    if (t < (m-1))
                    {
                        f->mark_variadic_over();
                    }
                }
                break;
            }
        }
    }


    #endif
    //end

	
	//printf("number of registers condition 3 is %s %d\n",f->get_name().c_str(), m);
    /* At this moment, we know that the argument registers m, m+1, ... 6 are
     * all read before write within the same basic block and in a consecutive
     * order. */
    
    /* CONDITION 4:
     * Ensure that the last m arguments that were (i) read before write, (ii)
     * read within the same block, and (iii) read in consecutive order, are all
     * written to the stack.
     * We do this by testing if for each read instruction, the stack pointer
     * (RSP) was read by the same instruction (this indicates that the read
     * before write instruction is likely to move the argument value to the
     * stack). TODO: if necessary, we make this check harder by keeping track of
     * memory writes.
     *
     * Unoptimized binaries may use the base pointer (RBP) instead of RSP which
     * is why we perform the test twice. 
     *
     * TODO? We thus currently enforce that the last non-vararg argument is no
     * longer in this set. I am not sure if this is always the case. */
    ddprintf("  [varargs.C4] Testing whether RSP/RBP was read...\n");
    if (!also_read(m, last_bb, IA64_RSP) && 
        !also_read(m, last_bb, IA64_RBP)) {
        /* Not all possible variadic arguments were stored on the stack.
         * Assuming not variadic. */
        return 0;
    }
    #endif
    #endif

return_label:
    /* we mark this <last_bb> as vararg-related so that we can use it later */
    last_bb->mark_vararg();
    
    //printf("number of registers condition 4 is %s %d\n",f->get_name().c_str(),m);

    return m;


    /* Now, when optimization is enabled, we wrongly detect:
     *
     * int test_va_working_func(int p0, int p1, ...) {
     *  va_list vl;
     *  va_start(vl, p1);
     *  va_end(vl);
     * }
     *
     * as a variadic function that expects 3 arguments. This is caused by the
     * compiler optimizing the use of p1 away. While this is valid code, of
     * course, I argue that this is a programming error.
     *
     * It happens for
     * - proftpd: src/scoreboard.c: pr_scoreboard_entry_update(pid_t pid, ...)
     * - openssh: openbsd-compat/setproctitle.c: setproctitle(const char *fmt, ...)
     */
}


/* Store read/write/clear state for 6 argument registers. We need two bits per
 * argument: 12 bits in total */
//uint16_t reg_bitmap;

/* As defined in arms_liveness.h:
 *   IA64_CLEAR     0x00    00b
 *   IA64_READ      0x01    01b
 *   IA64_WRITE     0x02    10b
 *   IA64_RW        0x03    11b
 */

/* set register <reg_index> to <state> */
void set_reg_bitmap(uint16_t *reg_bitmap, int reg_index, uint16_t state) {
    *reg_bitmap &= ~(0x03 << (reg_index * 2)); // clear first
    *reg_bitmap |= state << (reg_index * 2);
}

//added by yanlin STRATEGY_WIDTH
#ifdef STRATEGY_WIDTH
void set_width_bitmap(uint32_t *width_bitmap, int reg_index, uint16_t width) {
    *width_bitmap &= ~(0xf << (reg_index * 4)); // clear first
    *width_bitmap |= width << (reg_index * 4);
}
int get_width_bitmap(int width_bitmap, int reg_index) {
    return (width_bitmap >> (reg_index * 4) & 0xf);
}
#endif 

/* returns true if register <reg_index> is set to <state> */
bool is_reg_bitmap(int reg_bitmap, int reg_index, uint16_t state) {
    return (reg_bitmap >> (reg_index * 2) & 0x03) == state;
}

/* returns the state of register <reg_index> */
int get_reg_bitmap(int reg_bitmap, int reg_index) {
    return (reg_bitmap >> (reg_index * 2) & 0x03);
}

int bitmap_argset(int reg_bitmap, uint16_t state) {
    int argcount = 0;

    while (get_reg_bitmap(reg_bitmap, argcount) == state) {
        argcount++;
    }

    return argcount;
}

bool is_complete(int reg_bitmap, uint16_t state) {
    for (int i = 0; i < 6; i++) {
        if (is_reg_bitmap(reg_bitmap, i, state)) return false;
    }
    return true;
}


std::string ArmsLiveness::bm_tostring(int reg_bitmap) {
    string result = "";
    for (int i = 0; i < 6; i++) {
        if (is_reg_bitmap(reg_bitmap, i, IA64_CLEAR)) result += "C ";
        if (is_reg_bitmap(reg_bitmap, i, IA64_READ)) result += "R ";
        if (is_reg_bitmap(reg_bitmap, i, IA64_WRITE)) result += "W ";
        if (is_reg_bitmap(reg_bitmap, i, IA64_RW)) result += "X ";
    }
    return result;

}


//added by yanlin
bool ArmsLiveness::REGreads(ArmsFunction *f,
             ArmsBasicBlock *bb,
             std::vector<ArmsBasicBlock *> retuse_fts,
             std::vector<ArmsBasicBlock *> retuse_analyzed_blocks)
{
    for (int i = 0; i< IA64_ARGS; i++)
    {
        if (getREGreads(f,bb,0,i,retuse_fts,retuse_analyzed_blocks))
        {
            std::cout <<"find reg\n";
            ddprintf("reg number %d\n",i);
            return true;
        }
    }
    return false;
}

#ifdef CHECK_DCALL
int ArmsLiveness::DirectCallREGReads(ArmsFunction *f)
{
    int i = 0;
    for (std::set<ArmsBasicBlock *>::iterator it  = call_blocks[f].begin();
                                              it != call_blocks[f].end();
                                              it++, i++) {
        ArmsBasicBlock *block = *it;
        unsigned long call_addr = block->get_last_insn_address();
        ddprintf("\n%s() got direct call in basic block: %p\n", f->get_name().c_str(), (void*)block->get_start_address());


        std::vector<ArmsBasicBlock *> retuse_analyzed_blocks;
        std::vector<ArmsBasicBlock *> retuse_fts;
        if (block->get_fallthrough_bb() == NULL)
        {
            return 0;
        }

        ArmsBasicBlock *fallthrough_bb = block->get_fallthrough_bb();

        unsigned long start_addr = fallthrough_bb->get_start_address();

        if ((start_addr - call_addr) > 5)
            return 0;
        
        std::map<address_t, ArmsFunction *>::iterator it_f = all_functions.find(start_addr);
	    if (it_f != all_functions.end())
		    return 0;

        ParseAPI::Block *pblock = (ParseAPI::Block *) fallthrough_bb->get_parse_block();
        if (!pblock) return 0; // TODO

        /* Parse the instructions of this basic block */
        ParseAPI::Block::Insns insns;
        pblock->getInsns(insns);
        //added by yanlin
        if (insns.size() == 0)
            return 0; 
        ParseAPI::Block::Insns::iterator itt  = insns.begin(); 
        if (!itt->second->isLegalInsn())
            return 0;
        
        if (isNop(itt->second))
            return 0;


        if (REGreads(f, block->get_fallthrough_bb(),retuse_fts, retuse_analyzed_blocks))
            ddprintf("!! direct callsite %s.%d (%p) reads REG !!\n", f->get_name().c_str(), i, (void *)block->get_last_insn_address());

    }
    return 0;

}
#endif

//added by yanlin
bool ArmsLiveness::getREGreads(ArmsFunction *f,
                                ArmsBasicBlock *bb,
                                int depth,
                                int reg,
                                std::vector<ArmsBasicBlock *> retuse_fts,
                                std::vector<ArmsBasicBlock *> retuse_analyzed_blocks)
{
    StateType state;
    depth++;
    
    int edges_followed = 0;

    std::vector<bool> bitmaps;
    std::string blanks(retuse_analyzed_blocks.size(), ' ');

    state = rw_registers[reg].getState(bb);

    if (state == IA64_READ)   {
        return true;
    }

    if (state == IA64_WRITE || state == IA64_RW)
        return false;
    if (state == IA64_CLEAR)
    {
        if (bb->outgoing_edge_count() == 0) {
            /* If this block has no outgoing edges, we must stop. */
            return false;
           
        }
        retuse_analyzed_blocks.insert(retuse_analyzed_blocks.begin(), bb);


        for (size_t i = 0; i < bb->outgoing_edge_count(); i++) {
            bitmaps.push_back(false);

            ArmsEdge *edge = bb->get_outgoing_edge(i);
            ArmsBasicBlock *next_bb = NULL;
            ArmsBasicBlock *fallthrough_bb = NULL;

            ddprintf("[ret-ft]%s Edge %lu/%lu ",blanks.c_str(),i+1,bb->outgoing_edge_count());

            if (edge->is_return()) {
                /* do we have a fallthrough to follow? */
                if (!retuse_fts.empty()) {
                    ddprintf("is return, continuing at fallthrough\n");
                    next_bb = retuse_fts.back();
                    retuse_fts.pop_back();
                    assert(false);
                } else {
                    ddprintf("is return, but not fallthrough found. End of function?\n");
                    return false;
                    
                }
            } else if (edge->is_direct_call()) {
                // FIXME we must return here
                //return false;
                break;
                /* TODO maybe we can omit this if we're assuming standard calling convention. the 
                * compiler may optimize this. if the callee needs the return value as an argument, it
                * does not necessarily have to be moved into an argument register. */
                ddprintf("is direct call, storing fallthrough\n");

                next_bb = edge->target();
                fallthrough_bb = bb->get_fallthrough_bb();

                
        
                assert(next_bb != NULL);
               

                /* some direct calls never return, in which case we do not look at
                * the fallthrough. */
                if (fallthrough_bb == NULL) {
                    ddprintf("[ret-ft]%s fallthrough is null. assuming non-returning\n", blanks.c_str());
                } else if (isNop(fallthrough_bb)) {
                    ddprintf("[ret-ft]%s fallthrough is nop. assuming non-returning\n", blanks.c_str());
                    fallthrough_bb = NULL;
                } else if (fallthrough_bb->is_entry_block()) {
                    ddprintf("[ret-ft]%s fallthrough is entry block. assuming non-returning\n", blanks.c_str());
                    fallthrough_bb = NULL;
                } else {
                    ddprintf("[ret-ft]%s fallthr: %p\n", blanks.c_str(), (void *)fallthrough_bb->get_start_address());
                    
                    if (next_bb->get_function() != NULL &&
                        next_bb->get_function()->is_plt()) {
                    
                        if (next_bb->get_function()->get_name() == "exit") {
                            ddprintf("[ret-ft]%s direct call to exit@plt, non returning\n", blanks.c_str());
                            fallthrough_bb = NULL;
                        } else {
                            ddprintf("[ret-ft]%s direct call to PLT stub, continuing straight at fallthrough\n", blanks.c_str());
                            next_bb = fallthrough_bb;
                        }
                    } else {
                        retuse_fts.push_back(fallthrough_bb);
                    }
                }
            } else if (edge->is_indirect_call()) {
                ddprintf("is indirect call, we must assume the target does not reads rax\n");
    //          assert(bb->outgoing_edge_count() == 1);
                return false;
            } else {
                ddprintf("is regular\n");
                next_bb = edge->target();
            }

            assert(next_bb != NULL);
            

            if (next_bb->get_function() == NULL) {
                /* FIXME this bb is part of multiple functions, we must stop */
                return false;
                
            }
            if (next_bb->get_function() != f) {
                /* FIXME */
                return false;
                
            }

            ddprintf("[ret-ft]%s Next block: %p\n", blanks.c_str(), (void *) next_bb->get_start_address());

            if (std::find(retuse_analyzed_blocks.begin(),
                        retuse_analyzed_blocks.end(),
                        next_bb) != retuse_analyzed_blocks.end()) {
                ddprintf("[ret-ft]%s Next block is already analyzed (loop detection)\n", blanks.c_str());
                bitmaps[i] = true; /* assuming worst-case */
                continue;
            }

            ddprintf("[ret-ft]%s Entering recursing\n",blanks.c_str());
            if (depth < 15)
                bitmaps[i] = this->getREGreads(f, next_bb, depth, reg, retuse_fts, retuse_analyzed_blocks);
            else
                return false;
                
            edges_followed++;
        }
            
        ddprintf("[ret-ft]%s followed %d edges\n", blanks.c_str(), edges_followed);

        if (edges_followed == 0) {
            ddprintf("[ret-ft]%s No edges followed\n", blanks.c_str());
            return false;
            
        }

        ddprintf("[ret-ft]%s Computing best bitmap\n", blanks.c_str());
        for (auto it  = bitmaps.begin(); 
                it != bitmaps.end();
                it++) {
            bool bitmap = *it;

            /* all paths must read before write rax */
            if (bitmap == false)   return false;
        }
        return true;
    }

}
//end of yanlin

bool ArmsLiveness::getRAXreads(ArmsFunction *f,
                                   ArmsBasicBlock *bb,
                                   std::vector<ArmsBasicBlock *> retuse_fts,
                                   std::vector<ArmsBasicBlock *> retuse_analyzed_blocks) {   

    int edges_followed = 0;

    std::vector<bool> bitmaps;
    std::string blanks(retuse_analyzed_blocks.size(), ' ');

    StateType state;
    //changed by yanlin
    state = rw_registers[IA64_RAX].getState(bb);
    //original
    //state = rw_registers[IA64_RAX].getState(bb);
    if (state == IA64_READ)   {
        return true;
    }
    if (state == IA64_WRITE ||
        state == IA64_RW) {
        return false;
    }

    


    /* state == IA64_CLEAR (rax was not touched) */
    
    if (bb->outgoing_edge_count() == 0) {
        /* If this block has no outgoing edges, we must stop. */
        return false;
    }

    
    retuse_analyzed_blocks.insert(retuse_analyzed_blocks.begin(), bb);


    for (size_t i = 0; i < bb->outgoing_edge_count(); i++) {
        bitmaps.push_back(false);

        ArmsEdge *edge = bb->get_outgoing_edge(i);
        ArmsBasicBlock *next_bb = NULL;
        ArmsBasicBlock *fallthrough_bb = NULL;

        ddprintf("[ret-ft]%s Edge %lu/%lu ",blanks.c_str(),i+1,bb->outgoing_edge_count());

        if (edge->is_return()) {
            /* do we have a fallthrough to follow? */
            if (!retuse_fts.empty()) {
                ddprintf("is return, continuing at fallthrough\n");
                next_bb = retuse_fts.back();
                retuse_fts.pop_back();
                assert(false);
            } else {
                ddprintf("is return, but not fallthrough found. End of function?\n");
                return false;
            }
        } else if (edge->is_direct_call()) {
            // FIXME we must return here
            return false;
              
            /* TODO maybe we can omit this if we're assuming standard calling convention. the 
             * compiler may optimize this. if the callee needs the return value as an argument, it
             * does not necessarily have to be moved into an argument register. */
            ddprintf("is direct call, storing fallthrough\n");

            next_bb = edge->target();
            fallthrough_bb = bb->get_fallthrough_bb();

            
       
            assert(next_bb != NULL);

            /* some direct calls never return, in which case we do not look at
             * the fallthrough. */
            if (fallthrough_bb == NULL) {
                ddprintf("[ret-ft]%s fallthrough is null. assuming non-returning\n", blanks.c_str());
            } else if (isNop(fallthrough_bb)) {
                ddprintf("[ret-ft]%s fallthrough is nop. assuming non-returning\n", blanks.c_str());
                fallthrough_bb = NULL;
            } else if (fallthrough_bb->is_entry_block()) {
                ddprintf("[ret-ft]%s fallthrough is entry block. assuming non-returning\n", blanks.c_str());
                fallthrough_bb = NULL;
            } else {
                ddprintf("[ret-ft]%s fallthr: %p\n", blanks.c_str(), (void *)fallthrough_bb->get_start_address());
                
                if (next_bb->get_function() != NULL &&
                    next_bb->get_function()->is_plt()) {
                
                    if (next_bb->get_function()->get_name() == "exit") {
                        ddprintf("[ret-ft]%s direct call to exit@plt, non returning\n", blanks.c_str());
                        fallthrough_bb = NULL;
                    } else {
                        ddprintf("[ret-ft]%s direct call to PLT stub, continuing straight at fallthrough\n", blanks.c_str());
                        next_bb = fallthrough_bb;
                    }
                } else {
                    retuse_fts.push_back(fallthrough_bb);
                }
            }
        } else if (edge->is_indirect_call()) {
            ddprintf("is indirect call, we must assume the target does not reads rax\n");
//          assert(bb->outgoing_edge_count() == 1);
            return false;
        } else {
            ddprintf("is regular\n");
            next_bb = edge->target();
        }

        assert(next_bb != NULL);

        if (next_bb->get_function() == NULL) {
            /* FIXME this bb is part of multiple functions, we must stop */
            return false;
        }
        if (next_bb->get_function() != f) {
            /* FIXME */
            return false;
        }

        ddprintf("[ret-ft]%s Next block: %p\n", blanks.c_str(), (void *) next_bb->get_start_address());

        if (std::find(retuse_analyzed_blocks.begin(),
                      retuse_analyzed_blocks.end(),
                      next_bb) != retuse_analyzed_blocks.end()) {
            ddprintf("[ret-ft]%s Next block is already analyzed (loop detection)\n", blanks.c_str());
            bitmaps[i] = true; /* assuming worst-case */
            continue;
        }

        ddprintf("[ret-ft]%s Entering recursing\n",blanks.c_str());
        bitmaps[i] = this->getRAXreads(f, next_bb, retuse_fts, retuse_analyzed_blocks);
        
        edges_followed++;
    }
        
    ddprintf("[ret-ft]%s followed %d edges\n", blanks.c_str(), edges_followed);

    if (edges_followed == 0) {
        ddprintf("[ret-ft]%s No edges followed\n", blanks.c_str());
        return false;
    }

    ddprintf("[ret-ft]%s Computing best bitmap\n", blanks.c_str());
    for (auto it  = bitmaps.begin(); 
              it != bitmaps.end();
              it++) {
        bool bitmap = *it;

        /* all paths must read before write rax */
        if (bitmap == false) return false;
    }
    return true;
}



std::vector<uint32_t> ArmsLiveness::getBackwardLiveness(ArmsFunction *f,
                                       ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> &callsite_analyzed_blocks, int depth,
            unsigned long icall_addr, std::vector<int>first_write) {

    int edges_followed = 0;
    uint16_t *bitmaps;

    std::string blanks(callsite_analyzed_blocks.size(), ' ');

    ddprintf("[bt]%s Block status for %p: ",blanks.c_str(), (void *)bb->get_start_address());


    uint16_t reg_bitmap = 0;
    for (int i = 0; i < IA64_ARGS; i++) {
        set_reg_bitmap(&reg_bitmap, i, IA64_READ);
    }


    #ifdef STRATEGY_WIDTH
    uint32_t *reg_widths;

    uint32_t width_bitmap = 0xffffff;

    for (int i = 0; i < IA64_ARGS; i++) {
        set_width_bitmap(&width_bitmap, i, 0);
    }
    #endif 

    //added by yanlin, first check whether this basic block is analyzed,
    if (!is_analyzed(bb))
    {
        #ifdef PARSE_DATA_SECTION
        std::vector<std::vector<unsigned long>>data_info;
        std::vector<unsigned long> text;
        text.push_back(0xffffff);
        text.push_back(0xffffff);

        std::vector<unsigned long> rodata;
        rodata.push_back(0xffffff);
        rodata.push_back(0xffffff);

        std::vector<unsigned long> bss;
        bss.push_back(0xffffff);
        bss.push_back(0xffffff);

        data_info.push_back(rodata);
        data_info.push_back(bss);
        data_info.push_back(text);


        this->parse_block(f,bb,data_info);
        #else
        this->parse_block(f,bb);
        #endif
    }

    /* update the callsite_registers with information from the current block */
    /* defaults to read. if a register get trashed, we mark it as clear; else written */
    bool done = true;
    std::map<int, std::set<unsigned int>> reg_offset;
    std::map<int, std::set<unsigned int>> reg_offset_other;
    std::map<std::pair<int,unsigned int>, unsigned int> reg_offset_reg;

    #ifdef TEMPORARY
    if (bb->get_last_insn_address() == icall_addr)
    {
        for (int i = 0; i < IA64_ARGS; i++)
        {
            int first_write = 0;
            ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();

            ParseAPI::Block::Insns insns;
            pblock->getInsns(insns);
            int reg_index = -1;
            for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                                it != insns.end(); 
                                                it++) 
            {
                /* it->first:  offset
                * it->second: instruction */
                
                if (rw_registers[i].getState(bb,it->first) == IA64_RW || 
                    rw_registers[i].getState(bb,it->first) == IA64_WRITE && first_write == 0)
                {
                       
                    RegisterAST::Ptr reg = rw_registers[i].readARGtoARG(bb,it->second,it->first);
                    if (reg)
                    {
                        reg_index = get_reg_index(reg);
                        if (reg_index != i && reg_index < IA64_ARGS)
                        {
                            dprintf("reading arg to arg %d,%d\n",reg_index,i);
                            //if (reg_index > 0)
                            set_reg_bitmap(&reg_bitmap, reg_index, IA64_CLEAR);
                            reg_offset[reg_index].insert(it->first);
                            first_write = 1;
                        }
                        if (reg_index >= IA64_ARGS)
                        {
                            auto p = std::make_pair(reg_index, it->first);
                            reg_offset_other[reg_index].insert(it->first);
                            reg_offset_reg[p] = i;
                        }
                    }
                }

                if (rw_registers[i].getState(bb,it->first) == IA64_RW || 
                    rw_registers[i].getState(bb,it->first) == IA64_WRITE && first_write == 1)
                {
                    RegisterAST::Ptr reg = rw_registers[i].readARGtoARG(bb,it->second,it->first);
                    if (!reg)
                    {
                        if (reg_index != -1)
                        {
                            set_reg_bitmap(&reg_bitmap, reg_index, IA64_READ);
                            if (rw_registers[reg_index].writtenInBlock(bb))
                                set_reg_bitmap(&reg_bitmap, reg_index, IA64_WRITE);
                        }
                    }
                }
                        
            }
        }
    }
    #endif
    
    /*
    #ifdef TEMPORARY
    if (bb->get_last_insn_address() == icall_addr)
    {
        for (int i = IA64_ARGS; i < IA64_REGS;i++)
        {
            if (reg_offset_other.find(i) != reg_offset_other.end())
            {
                dprintf("find other\n");
                ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();

                ParseAPI::Block::Insns insns;
                pblock->getInsns(insns);
                for (auto elem : reg_offset_other[i])
                {
                    dprintf("reg offset other %d,%lx\n",i,elem);
                    int last_write = 0;
                    Instruction::Ptr iptr;
                    ParseAPI::Block::Insns::iterator it;
                    for (it  = insns.begin(); it != insns.end(); it++)
                    {
                        if (it->first < elem)
                        {
                            if  (rw_registers[i].getState(bb,it->first) == IA64_WRITE)
                            {
                                last_write = it->first;
                                iptr = it->second;
                                
                            }
                        }
                    }
                    if (last_write)
                    {
                        dprintf("last write\n");
                        
                        std::vector<Operand> operands;
		
                        iptr->getOperands(operands);

                        std::string ins_str = iptr->format(0).c_str();

                        std::size_t found = ins_str.find("mov");

                        //dprintf("instruction info %s,lx\n",iptr->format(0).c_str(),offset);
                        if (found != std::string::npos)
                        {   
                            dprintf("find mov instruction %s,%lx\n",iptr->format(0).c_str(),last_write);    
                            if (operands.size() == 2)
                            {
                                Operand operand = operands[1];

                                OperandType operandType;
                                operand.getValue()->apply(&operandType);

                                std::string str =  operand.format(Arch_x86_64).c_str();

                                if (str.size() <= 3 && !operandType.immediate)
                                {
                                    std::set<RegisterAST::Ptr> register_set;

                                    iptr->getReadSet(register_set);
                                    for (std::set<RegisterAST::Ptr>::iterator itt  = register_set.begin(); 
                                                        itt != register_set.end(); 
                                                        itt++)
                                    {
                                        RegisterAST::Ptr reg = *itt;  
                                                        
                                    
                                        int reg_index = get_reg_index(reg);
                                        auto p = std::make_pair(i,elem);
                                        if (reg_index < IA64_ARGS && reg_index != reg_offset_reg[p] )
                                        {
                                            set_reg_bitmap(&reg_bitmap, reg_index, IA64_CLEAR);
                                            //done = false;
                                        }
                                        else if (reg_index == reg_offset_reg[p] && reg_index < IA64_ARGS)
                                        {
                                            set_reg_bitmap(&reg_bitmap, reg_index+1, IA64_CLEAR);
                                            //done = false;
                                        } 
                                    }
                                }
                            }
                        }
                        
                    }


                }

            }
        }
    }
    #endif*/

    for (int i = 0; i < IA64_ARGS; i++) {
        //if (is_reg_bitmap(reg_bitmap, i, IA64_CLEAR)) 
        int find_write = 0;
        {
            #ifdef TEMPORARY
            if (bb->get_last_insn_address()== icall_addr){

                ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();

                ParseAPI::Block::Insns insns;
                pblock->getInsns(insns);
                for (ParseAPI::Block::Insns::reverse_iterator it  = insns.rbegin(); 
                                                    it != insns.rend(); 
                                                    it++) {
                    /* it->first:  offset
                    * it->second: instruction */

                    if (rw_registers[i].getState(bb,it->first) == IA64_WRITE || 
                        rw_registers[i].getState(bb,it->first) == IA64_RW)
                    {
                        find_write = 1;
                        if (reg_offset.find(i) != reg_offset.end())
                        {
                            int last_read_offset = *reg_offset[i].rbegin();
                            dprintf("last read offset %lx,%d\n",last_read_offset,i);
                            if (last_read_offset < it->first)
                            {
                                set_reg_bitmap(&reg_bitmap, i, IA64_WRITE);
                            }
                            else{
                                std::vector<Operand> operands;
            
                                it->second->getOperands(operands);
                                if (operands.size() == 2)
                                {
                                    Operand operand = operands[1];

                                    OperandType operandType;
                                    operand.getValue()->apply(&operandType);

                                    if (operandType.immediate)
                                    {
                                        std::string str =  operand.format(Arch_x86_64).c_str();
                                        dprintf("string operand %s\n",str.c_str());
                                        if (IsThisStringAHexNumber(str) &&  str.find("P") == std::string::npos)
                                        {
                                            dprintf("find immediate\n");
                                            set_reg_bitmap(&reg_bitmap, i, IA64_WRITE);
                                        }
                                    }
                                }
                                else
                                {
                                    done = false;
                                }
                            }
                        }
                        else{
                            ddprintf("do not find read arg to arg instruction\n");
                            set_reg_bitmap(&reg_bitmap, i, IA64_WRITE);
                        }
                        
                    }
                    else
                    {
                        
                        done = false;
                    }
                            
                }
                if (!find_write)
                {
                    set_reg_bitmap(&reg_bitmap, i, IA64_READ);
                }
            }
            #endif
            
            if (rw_registers[i].writtenInBlock(bb))
            {
                /*our policy should use it*/
                //if (bb->get_last_insn_address() != icall_addr)
                set_reg_bitmap(&reg_bitmap, i, IA64_WRITE);
        

                #ifdef STRATEGY_WIDTH
                int width = width_registers[i].getWidth_callsite(bb);
                set_width_bitmap(&width_bitmap,i,width);
                #endif

                #ifdef SixToThree
                if (width !=0 && first_write[i] == 1)
                {
                    if (width == 8){
                        if (!BBR36[bb][i])
                        {
                            int Read32To64 = isBBRead32To64(bb,i);
                            if (Read32To64)
                            {
                                BBR36[bb][i] = 1;
                                //icall36 = 1;
                                icall_R36[icall_addr][i] = 1;
                                //printf("read 32 to 64 %lx,%lx\n",bb->get_start_address(),icall_addr);
                            }
                            BBR36[bb][i] = 8;

                        }
                        #ifdef PARSE_DATA_SECTION
                        BBConstant[bb][i] = 3;
                        //icall_constant[icall_addr][i] = 0;
                        #endif
                    }
                    
                    if (width == 4){

                        #ifdef CHECK_XOR

                        if (!BBicallXor[bb][i])
                        {
                            int icallXor = isBBXorIns(bb,i);
                            if (icallXor)
                            {
                                BBicallXor[bb][i] = 1;
                                icall_xor[icall_addr][i] = 1;
                            }
                            else 
                            {
                                int icallXorFirst = isBBXorFirst(bb,i);
                                if (icallXorFirst )
                                {
                                    BBicallXor[bb][i] = 1;
                                    icall_xor[icall_addr][i] = 1;
                                }
                            }
                            BBicallXor[bb][i] = 4;
                        }

                        #endif


                        if (!BBR13[bb][i])
                        {
                            int Read16To32 = isBBRead16To32(bb,i);
                            if (Read16To32)
                            {
                                BBR13[bb][i] = 1;
                                icall_R13[icall_addr][i] = 1;
                                //icall13 = 1;
                                //printf("read 16 to 32 %lx,%lx\n",bb->get_start_address(),icall_addr);
                            }
                            
                            BBR13[bb][i] = 4;

                        }
                        if (!BBConstant[bb][i])
                        {
                            int isConstant = isbbConstantArg(bb,i);
                            //int isConstant = 0;
                            if (isConstant)
                            {
                                BBConstant[bb][i] = isConstant;
                                icall_constant[icall_addr][i] = isConstant;
                                //icall_constant = isConstant;
                                
                            }
                            else
                            {
                                int isConstantfirst = isbbConstantArgFirst(bb,i);
                                if (isConstantfirst)
                                {
                                    BBConstant[bb][i] = isConstant;
                                    icall_constant[icall_addr][i] = isConstantfirst;
                                    //icall_constant = isConstant;
                                    
                                }
                            }
                            
                            BBConstant[bb][i] = 3;
                        }
                    }
                    first_write[i] = 0;
                }
                #endif
            }

            else {

                done = false;
            }
        }
        
        ddprintf("%d ",get_reg_bitmap(reg_bitmap, i));
    }
    ddprintf("(%x)\n",reg_bitmap);
    
    ddprintf("[bt]%s %p -> ", blanks.c_str(), (void*)bb->get_start_address());
    for (auto it  = callsite_analyzed_blocks.begin(); 
              it != callsite_analyzed_blocks.end();
              it++) {
        ArmsBasicBlock* analyzed_block = *it;
        ddprintf("%p -> ", (void *) analyzed_block->get_start_address());
    }
    dprintf("? (block has %x)\n",reg_bitmap);

    if (done) {
        ddprintf("[bt]%s All arguments set, returning\n", blanks.c_str());
        goto debug_return;
        //return reg_bitmap;
    }

    callsite_analyzed_blocks.insert(callsite_analyzed_blocks.begin(), bb);

    bitmaps = (uint16_t *) malloc(bb->incoming_edge_count() * sizeof(uint16_t)); 

    #ifdef STRATEGY_WIDTH
    reg_widths = (uint32_t *) malloc(bb->incoming_edge_count() * sizeof(uint32_t)); 
    #endif
    //added by yanlin
    if (bb->is_entry_block())
    {
        if (bb->incoming_edge_count() == 1 )
        {
            for (size_t i = 0; i < bb->incoming_edge_count(); i++)
            {
                ArmsEdge *edge_bb = bb->get_incoming_edge(i);
                if (!edge_bb->is_interprocedural())
                {
                    for (int j = 0; j < IA64_ARGS; j++) {
                        if (is_reg_bitmap(reg_bitmap, j, IA64_READ)) {
                            set_reg_bitmap(&reg_bitmap, j, IA64_WRITE);
                            #ifdef STRATEGY_WIDTH
                            set_width_bitmap(&width_bitmap,j,0x8);
                            #endif
                        }
                    }
                    //printf("indirect call in wrapper function without callers %lx\n",icall_addr);
                    icall_in_wrapper[icall_addr] = 1;
                    goto debug_return;
                    //return reg_bitmap;  
                }
            }
        }
    }
    //end

    if (bb->is_entry_block() && bb->incoming_edge_count() != 0)
    {
        icall_in_wrapper[icall_addr] = 2;
        //printf("indirect call in wrapper with callers %lx\n",icall_addr);
    }

    if (bb->is_entry_block() && bb->incoming_edge_count() == 0) {
        //printf("indirect call in wrapper without callers %lx\n",icall_addr);
        icall_in_wrapper[icall_addr] = 1;
        if (bb->get_function() == 0) {
            ddprintf("[bt] wtf %s\n",f->get_name().c_str());
        } else {
            ddprintf("could use a direct edge: %s\n", f->get_name().c_str());
        }
        f->add_dependency(bb->get_function());
        #ifndef unopt
        for (int i = 0; i < IA64_ARGS; i++) {
            if (is_reg_bitmap(reg_bitmap, i, IA64_READ)) {
                set_reg_bitmap(&reg_bitmap, i, IA64_WRITE);
                #ifdef STRATEGY_WIDTH
                set_width_bitmap(&width_bitmap,i,0x8);
                #endif
            }
        }
        #endif
    }

    /* Loop recursively over the incoming edges for this basic block */
    for (size_t i = 0; i < bb->incoming_edge_count(); i++) {

        bitmaps[i] = reg_bitmap;

        #ifdef STRATEGY_WIDTH
        reg_widths[i] = width_bitmap;
        #endif

        ArmsEdge *edge = bb->get_incoming_edge(i);
        ArmsBasicBlock *prev_bb;

        ddprintf("[bt]%s Edge %lu/%lu\n",blanks.c_str(),i+1,bb->incoming_edge_count());

        if (bb->is_entry_block() && !edge->is_interprocedural())
            continue;
        
        if (edge->is_return()) {
            ddprintf("[bt]%s Edge is return, flushing\n", blanks.c_str());
            ddprintf("[bt]%s Updated block status: ", blanks.c_str());
            for (int j = 0; j < IA64_ARGS; j++) {
                if (is_reg_bitmap(bitmaps[i],j,IA64_READ)) {
                    set_reg_bitmap(&bitmaps[i], j, IA64_CLEAR);

                    #ifdef STRATEGY_WIDTH
                    set_width_bitmap(&width_bitmap,j,0x0);
                    #endif
                }
                ddprintf("%d ",get_reg_bitmap(bitmaps[i],j));
            }
            ddprintf("(%x)\n",bitmaps[i]);
            reg_bitmap = bitmaps[i];
            width_bitmap = reg_widths[i];
            free(bitmaps);
            //* there may be more edges, but it won't get better than this.
            // * return here 
            // *It is not true, how about different paths to the same caller

            goto debug_return;
            //return reg_bitmap;


        } else if (edge->is_direct_call() || edge->is_indirect_call()) {
            #ifndef opt
            ddprintf("[bt]%s Edge is direct call\n",blanks.c_str());
            //* Simply continue the backward search. This is a function that called us 
            prev_bb = edge->source();
            #endif
            //depth += 1;
        } else {
            ddprintf("[bt]%s Edge is regular\n",blanks.c_str());
            if(!edge->is_interprocedural() &&  bb->is_entry_block())
            {
                continue;
            }
            prev_bb = edge->source();
            

              
        }

        assert(prev_bb != NULL);

        ddprintf("[bt]%s Previous block: %p\n", blanks.c_str(), (void *) prev_bb->get_start_address());

        if (std::find(callsite_analyzed_blocks.begin(),
                      callsite_analyzed_blocks.end(),
                      prev_bb) != callsite_analyzed_blocks.end()) {
            ddprintf("[bt]%s Previous block is already analyzed\n", blanks.c_str());
            bitmaps[i] = 0xaaa; // * assume all WRITE TODO shouldn't this be all CLEAR? (0x000) 
            edges_followed++;
            continue;
        }

        
        for ( int j = 0; j<IA64_ARGS; j++)
        {
            #ifdef SixToThree
            BBR36[prev_bb][j] = 0;
            BBR13[prev_bb][j] = 0;
            if (BBR36[bb][j])
            {
                BBR36[prev_bb][j] = 2;
                BBR13[prev_bb][j] = 2;
            }
            else if (BBR13[bb][j])
            {
                BBR13[prev_bb][j] = 2;
                BBR36[prev_bb][j] = 0;
            }
            #endif

            #ifdef CHECK_XOR
            BBicallXor[prev_bb][i] = 0;
            if (BBicallXor[bb][i])
            {
                BBicallXor[prev_bb][i] = 3;
            }
            #endif

            #ifdef PARSE_DATA_SECTION
            BBConstant[prev_bb][j] = 0;
            if (BBConstant[bb][j])
            {
                BBConstant[prev_bb][j] = 3;
            }
            #endif
            
        }
        

        if (backward_cache.count(prev_bb)) {
            ddprintf("[bt]%s Cache lookup\n",blanks.c_str());
            bitmaps[edges_followed] = backward_cache[prev_bb];
        } else {
            ddprintf("[bt]%s Entering recursing\n",blanks.c_str());
            if ( depth < 10)
            {
                std::vector<uint32_t> info;
                info = this->getBackwardLiveness(f, prev_bb, callsite_analyzed_blocks,depth,icall_addr,first_write);
                bitmaps[edges_followed] = info[0];
                #ifdef STRATEGY_WIDTH
                reg_widths[edges_followed] = info[1];
                #endif
                backward_cache[prev_bb] = bitmaps[edges_followed];
            }
            else{
                for (int t = 0; t < IA64_ARGS; t++) {
                    if (is_reg_bitmap(reg_bitmap, t, IA64_READ)) {
                        set_reg_bitmap(&reg_bitmap, t, IA64_WRITE);
                    }
                } 
                goto debug_return;
                //return reg_bitmap;
            }
            
        }

        ddprintf("[bt]%s Got bitmap %x\n", blanks.c_str(), bitmaps[edges_followed]);
        assert(is_complete(bitmaps[edges_followed], IA64_READ));
        
        edges_followed++;
    }


    /* we now have our own bitmap <reg_bitmap> and a set of complete bitmaps.
     * get the best complete bitmap and combine it with ours */
    
    if (edges_followed == 0) {
//      ddprintf("[bt]%s best_bitmap = %x | reg_bitmap = %x\n", blanks.c_str(), best_bitmap, reg_bitmap);

        /* this means that no edges were found. we'll flush */
        ddprintf("[bt]%s No edges found, flushing\n", blanks.c_str());
        ddprintf("[bt]%s Updated block status: ", blanks.c_str());
        for (int j = 0; j < IA64_ARGS; j++) {
            if (is_reg_bitmap(reg_bitmap,j,IA64_READ)) {
                set_reg_bitmap(&reg_bitmap, j, IA64_CLEAR);

                #ifdef STRATEGY_WIDTH
                set_width_bitmap(&width_bitmap, j, 0x0);
                #endif
            }
            ddprintf("%d ",get_reg_bitmap(reg_bitmap,j));
        }
        ddprintf("(%x)\n",reg_bitmap);
    } else {
        ddprintf("number of edge followed %d\n",edges_followed);
    
        uint16_t best_bitmap = 0xaaa;
        #ifdef STRATEGY_WIDTH
        uint32_t best_width_bitmap = 0x0;
        #endif
        for (size_t i = 0; i < edges_followed; i++) {
            assert(is_complete(bitmaps[i], IA64_READ));
           
#ifdef CONSERVATIVE_CALLSITE
            if (bitmap_argset(bitmaps[i], IA64_WRITE) >= bitmap_argset(best_bitmap, IA64_WRITE)) {
                best_bitmap = bitmaps[i];
            }
#else
            if (bitmap_argset(bitmaps[i], IA64_WRITE) <= bitmap_argset(best_bitmap, IA64_WRITE)) {
                best_bitmap = bitmaps[i];
                
            }   
            #ifdef STRATEGY_WIDTH
            for (int t = 0 ; t < IA64_ARGS; t++)
            {
                if (get_width_bitmap(reg_widths[i],t) > get_width_bitmap(best_width_bitmap,t))
                {
                    set_width_bitmap(&best_width_bitmap, t, get_width_bitmap(reg_widths[i],t));
                    //best_width_bitmap = reg_widths[i];
                }
               
            }
            #endif
#endif
        }

        #ifdef STRATEGY_WIDTH
        ddprintf("width bitmap %x\n",width_bitmap);
        ddprintf("best width bitmap %x\n",best_width_bitmap);
        for (int i = 0; i < IA64_ARGS; i++)
        {
            int width = get_width_bitmap(width_bitmap,i);
            int width_best = get_width_bitmap(best_width_bitmap,i);
            //if (width == 4)
                //set_width_bitmap(&width_bitmap,i,0x4);
            if ( width_best > width)
                set_width_bitmap(&width_bitmap,i,width_best);
            /*if (is_reg_bitmap(reg_bitmap, i, IA64_READ))
            {
                set_width_bitmap(&width_bitmap,i,width_best);
            }
            else
            {

            }*/
        }
        #endif

        /* combine */
        ddprintf("[bt]%s Combining with %x\n", blanks.c_str(), best_bitmap);
        ddprintf("[bt]%s Updated block status: ", blanks.c_str());
        for (int i = 0; i < IA64_ARGS; i++) {
            if (is_reg_bitmap(reg_bitmap, i, IA64_READ)) {
                set_reg_bitmap(&reg_bitmap, i, get_reg_bitmap(best_bitmap,i));
            }
            ddprintf("%d ", get_reg_bitmap(reg_bitmap, i));
        }
        ddprintf("(%x)\n",reg_bitmap);
    }

    free(bitmaps);
    ddprintf("[bt]%s Processed all edges, returning our best bitmap (%x)\n", blanks.c_str(), reg_bitmap);
    goto debug_return;
    //return reg_bitmap;


debug_return:
    ddprintf("return [bt]%s ", blanks.c_str());
    for (auto it  = callsite_analyzed_blocks.begin(); 
              it != callsite_analyzed_blocks.end();
              it++) {
        ArmsBasicBlock* analyzed_block = *it;
        ddprintf("%p -> ", (void *) analyzed_block->get_start_address());
    }
    ddprintf("(%x)\n", reg_bitmap);
    std::vector<uint32_t> result;
    result.push_back(reg_bitmap);
    result.push_back(width_bitmap);
    return result;



}


/* based on getBackwardLiveness. we start at the exit point and move back to search for writes on rax */
bool ArmsLiveness::getRAXwrites(ArmsFunction *f,
                                    ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> callee_retuse_analyzed_blocks) {

    int edges_followed = 0;
    bool *bitmaps;

    std::string blanks(callee_retuse_analyzed_blocks.size(), ' ');

    if (rw_registers[IA64_RAX].writtenInBlock(bb)) {
        dprintf("[ret-bt]%s RAX is written in block\n", blanks.c_str());
        return true;
    }    

    callee_retuse_analyzed_blocks.insert(callee_retuse_analyzed_blocks.begin(), bb);

    bitmaps = (bool *) malloc(bb->incoming_edge_count() * sizeof(bool)); 

    if (bb->is_entry_block() && bb->incoming_edge_count() == 0) {
        /* no incoming edges - it could be an AT function that must be called. we can 
         * return false here (rax is not written) because we do not have to take possible 
         * callers into account (these are the callsites that expect rax to be written) */
        return false;
    }

    /* Loop recursively over the incoming edges for this basic block */
    for (size_t i = 0; i < bb->incoming_edge_count(); i++) {

        bitmaps[i] = false;

        ArmsEdge *edge = bb->get_incoming_edge(i);
        ArmsBasicBlock *prev_bb;

        ddprintf("[ret-bt]%s Edge %lu/%lu\n",blanks.c_str(),i+1,bb->incoming_edge_count());

        if (edge->is_return()) {
            ddprintf("[ret-bt]%s Edge is return, we must look at the called function\n", blanks.c_str());
            /* TODO assuming a write for now */
            return true;
        } else if (edge->is_direct_call() || edge->is_indirect_call()) {
            ddprintf("[ret-bt]%s Edge is direct call\n",blanks.c_str());
            /* Here we can stop, unless we implement previous mentioned TODO */
            return false;
        } else {
            ddprintf("[ret-bt]%s Edge is regular\n",blanks.c_str());
            prev_bb = edge->source();
        }

        assert(prev_bb != NULL);

        ddprintf("[ret-bt]%s Previous block: %p\n", blanks.c_str(), (void *) prev_bb->get_start_address());

        if (std::find(callee_retuse_analyzed_blocks.begin(),
                      callee_retuse_analyzed_blocks.end(),
                      prev_bb) != callee_retuse_analyzed_blocks.end()) {
            ddprintf("[ret-bt]%s Previous block is already analyzed\n", blanks.c_str());
            bitmaps[i] = true; /* assume all WRITE - worst case scenario */
            edges_followed++;
            continue;
        }

        ddprintf("[ret-bt]%s Entering recursing\n",blanks.c_str());
        //bitmaps[edges_followed] = this->getRAXwrites(f, prev_bb, callee_retuse_analyzed_blocks);
// patch Enes
        if(this->getRAXwrites(f, prev_bb, callee_retuse_analyzed_blocks)){
          free(bitmaps);
          return true;
        }else{
          bitmaps[edges_followed] = false;
        }
// patch Enes done

        ddprintf("[ret-bt]%s Got bitmap %x\n", blanks.c_str(), bitmaps[edges_followed]);
        
        edges_followed++;
    }


    /* we now have our own bitmap (false) and a set of complete bitmaps.
     * get the best complete bitmap and combine it with ours */
    
    if (edges_followed == 0) {
//      ddprintf("[bt]%s best_bitmap = %x | reg_bitmap = %x\n", blanks.c_str(), best_bitmap, reg_bitmap);
        
        
        /* the previous bb could have ended with an (indirect) call */
        if (!bb->is_entry_block()) {
            ArmsBasicBlock *up = bb->get_fallup_bb();
            if (up != NULL) {
                dprintf("[ret-bt] fount fallup\n");
                if (up->outgoing_edge_count() == 1) {
                    if (up->get_outgoing_edge(0)->is_indirect_call()) {
                        dprintf("[ret-bt] outgoing edge of up is indirect call");
                        return true;
                    }
                    if (up->get_outgoing_edge(0)->is_direct_call()) {
                        dprintf("[ret-bt] outgoing edge of up is direct call");
                        return true;
                        // TODO we can continue analysis instead of returning immediately
                    }
                }
            }
        }

        /* this means that no edges were found. we'll flush */
        ddprintf("[ret-bt]%s No edges found, flushing\n", blanks.c_str());
        return false;
    } 
    
    uint16_t all_true = true;

    /* rax must be written on all paths */
    for (size_t i = 0; i < edges_followed; i++) {
        if (bitmaps[i] == false) {
            all_true = false;
            break;
        }
    }

    free(bitmaps);
    ddprintf("[bt]%s Processed all edges, returning our best bitmap (%x)\n", blanks.c_str(), all_true);
    return all_true;

}




std::vector<uint32_t> ArmsLiveness::getForwardLiveness2(ArmsFunction *f,
                                       ArmsBasicBlock *bb,
                                       ArmsBasicBlock *prevBB,
                                       std::vector<ArmsBasicBlock *> fts,
                                       std::vector<ArmsBasicBlock *> argcount_analyzed_blocks,
                                       std::vector<uint16_t> *reg_width,
                                       std::vector<int> first_flag) {   

    int edges_followed = 0;

    std::vector<uint16_t> bitmaps;
    std::string blanks(argcount_analyzed_blocks.size(), ' ');

    //struct result info;
    uint16_t reg_bitmap = 0;
    for (int i = 0; i < IA64_ARGS; i++) {
        set_reg_bitmap(&reg_bitmap, i, IA64_CLEAR);
    }
    //info.reg_bitmap = reg_bitmap

    //added by yanlin

    if (!is_analyzed(bb))
    {
        #ifdef PARSE_DATA_SECTION
        std::vector<std::vector<unsigned long>>data_info;
        std::vector<unsigned long> text;
        text.push_back(0xffffff);
        text.push_back(0xffffff);

        std::vector<unsigned long> rodata;
        rodata.push_back(0xffffff);
        rodata.push_back(0xffffff);

        std::vector<unsigned long> bss;
        bss.push_back(0xffffff);
        bss.push_back(0xffffff);

        data_info.push_back(rodata);
        data_info.push_back(bss);
        data_info.push_back(text);


        this->parse_block(f,bb,data_info);
        #else
        this->parse_block(f,bb);
        #endif
    }


    std::vector<uint32_t> reg_widths;
    uint32_t width_bitmap = 0xffffff;
    for (int i = 0; i< IA64_ARGS; i++)
    {
        set_width_bitmap(&width_bitmap,i,0x9);
    }
    //end

    std::vector<uint32_t> read63_bitmaps;
    uint32_t read63_bitmap = 0xffffff;
    for (int i = 0; i< IA64_ARGS; i++)
    {
        set_width_bitmap(&read63_bitmap,i,0x9);
    }

    if (bb->get_start_address() == f->get_base_addr())
    {
        for (int j = 0; j < IA64_ARGS; j++)
            first_flag[j] = 1;
    }

    int is_Dcall = 0;
    int is_write = 0;




   
    /* Update the function_registers with information from the current block. */
    bool done = true;
    for (int i = 0; i < IA64_ARGS; i++) {
        if (is_reg_bitmap(reg_bitmap, i, IA64_CLEAR)) {

            StateType state;
            if (bb->is_vararg_mark()) {
                /* Stop if this block is vararg-related and responsible for
                 * writing the variadiac arguments to the stack.  
                 * The problem is that if we're in function F1, and we call
                 * variadic function F2 with 2 variaric arguments, then F2 will
                 * still write a the other arguments to the stack (and thus
                 * reads those arguments). This will result in false conclusions
                 * on the read-state of these registers.
                 */
                state = IA64_WRITE;
            } else {
                state = rw_registers[i].getState(bb);


                #ifdef STRATEGY_WIDTH

                if (state == IA64_WRITE || state == IA64_RW)
                {
                    first_flag[i] = 0;
                    //set_width_bitmap(&width_bitmap,i, 9);
                }
                
                if (state == IA64_READ)
                {
                    if (bb->get_start_address() != f->get_base_addr())
                    {
                        for (size_t j = 0; j < bb->incoming_edge_count(); j++) {

                            ArmsEdge *edge = bb->get_incoming_edge(j);
                            ArmsBasicBlock *prev_bb;

                            if (edge->is_direct_call())
                            {
                                prev_bb = edge->source();
                                if (width_registers[i].isWrite(prev_bb))
                                {
                                    is_write = 1;
                                }
                            }

                        }
                    }

                    if (!is_write)
                    {
                        first_flag[i] == 0;
                        int width = width_registers[i].getWidth_callee(bb);
                        dprintf("width test %lx %d\n",bb->get_start_address(),width);
                        if (width == 0)
                        {
                            width = 9;
                        }

                        set_width_bitmap(&width_bitmap,i, width);
                        
                        //dprintf("width bitmap %x\n",width_bitmap);
                        
                        if (width < function_argwidth[f->get_base_addr()][i])
                        {
                            //set_width_bitmap(&width_bitmap,i, width);
                            //dprintf("width index %d, %d\n",i,width);
                            function_argwidth[f->get_base_addr()][i] = width;
                        }
                        //if ( block_argwidth.count)
                        if (width < (*reg_width)[i])
                        {
                            (*reg_width)[i] = width;
                            //reg_widths[i] = width;
                        }
                        //set_width_bitmap(&width_bitmap,i, width); 
                    }
                    
                }
                else
                    set_width_bitmap(&width_bitmap,i, 0x9);
                #endif

                if (FunctionR63[f->get_base_addr()][i]==1  && state == IA64_WRITE)
                {
                    FunctionR63[f->get_base_addr()][i] = 0;
                }
                
                if (state == IA64_READ) {
                    
                    #ifdef SixToThree
                    {
                        int isread64To32 = isBBRead64To32(bb,i);
                        if (isread64To32)
                        {
                            set_width_bitmap(&read63_bitmap,i,0x8);
                           
                        }

                        int ispush_arg = isBBpush(bb,i);
                        if (ispush_arg)
                        {
                            #ifdef six2three_policy
                            set_width_bitmap(&read63_bitmap,i,0x8);
                            #endif
                        }
                    

                        /*if (FunctionR63[f->get_base_addr()][i])
                        {
                            int isread64To32 = isBBRead64To32(bb,i);
                            if (isread64To32)
                            {
                                dprintf("there is ins that reads 64 to 32-bit %s\n",f->get_name().c_str());
                                Fread64to32[f->get_base_addr()][i] = 1;
                                FunctionR63[f->get_base_addr()][i] = 0;

                                if (bb->is_entry_block())
                                {
                                    Fread64to32[bb->get_start_address()][i] = 1;
                                    FunctionR63[bb->get_start_address()][i] = 0; 
                                }
                            }
                            else
                            {
                                //printf("there is no ins that reads 64 to 32-bit %s\n",f->get_name().c_str());
                                FunctionR63[f->get_base_addr()][i] = 0;
                                if (bb->is_entry_block())
                                {
                                    FunctionR63[bb->get_start_address()][i] = 0; 
                                }
                            }
                        }*/
                    }
                    #endif
                    
                    if (rw_registers[i].getDeref(bb)) {
                        ddprintf("[ft] deref found\n");
                    }
                }
            }
                
            set_reg_bitmap(&reg_bitmap, i, state);
            

            if (state == IA64_CLEAR) {
                done = false;
            }

        }
    }
    
    ddprintf("[ft]%s blck_bitmap = %s (block %p)\n",blanks.c_str(), bm_tostring(reg_bitmap).c_str(), (void *)bb->get_start_address());
    
    prevBB = bb;
                
    if (bb->outgoing_edge_count() == 0) {
        /* If this block has no outgoing edges, we must stop. */
        done = true;
    }

    /* print process */
    ddprintf("[ft]%s ", blanks.c_str());
    for (auto rit  = argcount_analyzed_blocks.rbegin(); 
              rit != argcount_analyzed_blocks.rend();
              rit++) {
        ArmsBasicBlock* analyzed_block = *rit;
        ddprintf("%p <- ", (void *) analyzed_block->get_start_address());
    }
    ddprintf("%p ", (void*)bb->get_start_address());
    ddprintf("? (block has %x)\n",reg_bitmap);
    
    argcount_analyzed_blocks.insert(argcount_analyzed_blocks.begin(), bb);

    if (done) {
        ddprintf("[ft]%s All arguments processed, returning\n", blanks.c_str());
        goto ft_debug_return;
        /*std::vector<uint32_t> info_1;
        info_1.push_back(reg_bitmap);
        info_1.push_back(width_bitmap);


        return info_1;*/

        //return reg_bitmap;
        
        /*std::vector<uint16_t> info_1;
        info_1.push_back(reg_bitmap);
        for (int i=0; i< IA64_ARGS;i++)
        {
            info_1.push_back((*reg_width)[i]);
        }
        
        
        return info_1;*/
    }






    for (size_t i = 0; i < bb->outgoing_edge_count(); i++) {
    
        bitmaps.push_back(reg_bitmap);
        reg_widths.push_back(width_bitmap);
        read63_bitmaps.push_back(read63_bitmap);

        ArmsEdge *edge = bb->get_outgoing_edge(i);
        ArmsBasicBlock *next_bb = NULL;
        ArmsBasicBlock *fallthrough_bb = NULL;

        ddprintf("[ft]%s Edge %lu/%lu ",blanks.c_str(),i+1,bb->outgoing_edge_count());

    
        if (edge->is_return()) {
            /* do we have a fallthrough to follow? */
            if (!fts.empty()) {
                ddprintf("is return, continuing at fallthrough\n");
                next_bb = fts.back();
                fts.pop_back();
            } else {
                ddprintf("is return, but not fallthrough found. End of function?\n");
                reg_bitmap = bitmaps[i];
                width_bitmap = reg_widths[i];
                goto ft_debug_return;

                /*std::vector<uint32_t> info_2;
                info_2.push_back(reg_bitmap);
                info_2.push_back(width_bitmap);

                return info_2;*/
                //return reg_bitmap;
                /*std::vector<uint16_t> info_2;
                info_2.push_back(reg_bitmap);
                for (int i=0; i< IA64_ARGS;i++)
                {
                    info_2.push_back((*reg_width)[i]);
                }
                
                
                return info_2;*/
            }
        } else if (edge->is_direct_call()) {
            ddprintf("is direct call, storing fallthrough\n");
            
            next_bb = edge->target();
            //fallthrough_bb = bb->get_fallthrough_bb();
            fallthrough_bb = bb->get_fallthrough_bb_dcall();
       
            assert(next_bb != NULL);

           
            //first_flag[0] = 1;
            is_Dcall = 1;

            //* some direct calls never return, in which case we do not look at
            // * the fallthrough. 
            if (fallthrough_bb == NULL) {
                ddprintf("[ft]%s fallthrough is null. assuming non-returning\n", blanks.c_str());
            } else if (isNop(fallthrough_bb)) {
                ddprintf("[ft]%s fallthrough is nop. assuming non-returning\n", blanks.c_str());
                fallthrough_bb = NULL;
            } else if (fallthrough_bb->is_entry_block()) {
                ddprintf("[ft]%s fallthrough is entry block. assuming non-returning\n", blanks.c_str());
                fallthrough_bb = NULL;
            } else {
                ddprintf("[ft]%s fallthr: %p\n", blanks.c_str(), (void *)fallthrough_bb->get_start_address());
                
                if (next_bb->get_function() != NULL &&
                    next_bb->get_function()->is_plt()) {
                
                    if (next_bb->get_function()->get_name() == "exit") {
                        ddprintf("[ft]%s direct call to exit@plt, non returning\n", blanks.c_str());
                        fallthrough_bb = NULL;
                    } else {
                        ddprintf("[ft]%s direct call to PLT stub, continuing straight at fallthrough\n", blanks.c_str());
                        next_bb = fallthrough_bb;
                    }
                } else {
                    fts.push_back(fallthrough_bb);
                }
            }
        } else if (edge->is_indirect_call()) {
            // TODO: with profiling, the story becomes a bit different. I don't think it matters for now
            ddprintf("is indirect call, continuing at fallthrough\n");
//          assert(bb->outgoing_edge_count() == 1);

            fallthrough_bb = bb->get_fallthrough_bb();

            /* maybe there is icall tail optimization? - not supported*/
//          assert(fallthrough_bb != NULL);
            if (fallthrough_bb == NULL) {
                continue;
            }

//          assert(!fallthrough_bb->is_entry_block());
            if (fallthrough_bb->is_entry_block()) {
                /* let's assume this is not part of the same function */
                continue;
            }
//          assert(!isNop(fallthrough_bb));

            next_bb = fallthrough_bb;
        } 
        else {
            /* do not follow target of indirect jump as dyninst cannot resolve the correct
                for it*/
            if (edge_type_is_indirect_jmp(edge->type()))
            {
                continue;
            }
            ddprintf("is regular\n");
            next_bb = edge->target();
        }

        assert(next_bb != NULL);

        ddprintf("[ft]%s Next block: %p\n", blanks.c_str(), (void *) next_bb->get_start_address());

        if (std::find(argcount_analyzed_blocks.begin(),
                      argcount_analyzed_blocks.end(),
                      next_bb) != argcount_analyzed_blocks.end()) {
            ddprintf("[ft]%s Next block is already analyzed (loop detection)\n", blanks.c_str());
            bitmaps[i] = (0x0);
            continue;
        }
         
        if (forward_result.count(next_bb) ) {
            
            ddprintf("[ft]%s Cache lookup %lx\n",blanks.c_str(),next_bb->get_start_address());
            if (next_bb->is_entry_block())
                function_argwidth[f->get_base_addr()] = function_argwidth[next_bb->get_start_address()];
            /*else if (block_argwidth.count(next_bb)){
                //dprintf("next_bb is not entry block %lx\n",next_bb->get_start_address());
                for (int i = 0; i < IA64_REGS; i++)
                {
                    if (block_argwidth[next_bb][i] < function_argwidth[f->get_base_addr()][i])
                    {
                        function_argwidth[f->get_base_addr()][i] = block_argwidth[next_bb][i];
                    }
                }
            }
            else
            {
                dprintf("next_bb is not in block_argwidth %lx\n",next_bb->get_start_address());
            }*/
        } else {
            ddprintf("[ft]%s Entering recursing\n",blanks.c_str());
            forward_result[next_bb] = this->getForwardLiveness2(f, next_bb, prevBB, fts, argcount_analyzed_blocks,reg_width,first_flag);
            //block_argwidth[next_bb] = reg_width;
        }
        
        bitmaps[i] = forward_result[next_bb][0];
        reg_widths[i] = forward_result[next_bb][1];
        read63_bitmaps[i] = forward_result[next_bb][2];

        ddprintf("result %lx\n",forward_result[next_bb][1]);

        //dprintf("test *** %d\n",forward_result[next_bb][6]);
        
        /*std::vector<uint16_t>reg_width_info;
        //for (int i = 0; i< IA64_ARGS;i++)

        for (int i = 1; i< IA64_ARGS+1;i++)
        {
            dprintf("result %lx ",forward_result[next_bb][i]);
            reg_width_info.push_back(forward_result[next_bb][i]);
            //reg_width_info[i-1] = forward_result[next_bb][i];
        } 
        dprintf("\n");
        

        for ( int i = 0; i< IA64_ARGS; i++)
        {
            if (reg_width_info[i] < function_argwidth[f->get_base_addr()][i])
            {
                dprintf("caching result\n");
                function_argwidth[f->get_base_addr()][i] = reg_width_info[i];
            }
        }*/

        
        ddprintf("[ft]%s Got bitmap %x\n", blanks.c_str(), forward_cache[next_bb]);
        
        edges_followed++;
    }
        
    ddprintf("[ft]%s followed %d edges\n", blanks.c_str(), edges_followed);

    if (edges_followed == 0) {
        ddprintf("[ft]%s No edges followed\n", blanks.c_str());
    } else {
        uint16_t best_bitmap = 0xfff; /* start with worst-case, all clear */
        uint32_t best_width_bitmap = 0x999999;
        uint32_t best_read63_bitmap = 0x999999;
        ddprintf("[ft]%s Computing best bitmap\n", blanks.c_str());
        dprintf("[ft]%s blck_bitmap = %s (block %p)\n",blanks.c_str(), bm_tostring(reg_bitmap).c_str(), (void *)bb->get_start_address());
        
        /*for (auto it  = bitmaps.begin(); 
                  it != bitmaps.end();
                  it++) {*/
        for ( int t = 0 ; t < edges_followed; t++){
            //uint16_t bitmap = *it;
            uint16_t bitmap = bitmaps[t];
            uint32_t widthmap = reg_widths[t];
            uint32_t R63bitmap = read63_bitmaps[t];

            ddprintf("widthmap %lx\n",widthmap);
            ddprintf("best width bitmap %lx\n",best_width_bitmap);


            ddprintf("[ft]%s      bitmap = %s\n", blanks.c_str(), bm_tostring(bitmap).c_str());
            for (int i = 0; i < IA64_ARGS; i++) {

#ifdef ALLOW_UNINITIALIZED_READ
				
                if (is_reg_bitmap(best_bitmap, i, 0x3)) {
                    // if no state found yet, use the child's state 
                    set_reg_bitmap(&best_bitmap, i, get_reg_bitmap(bitmap, i));
                    #ifdef STRATEGY_WIDTH
                    set_width_bitmap(&best_width_bitmap,i,get_width_bitmap(widthmap,i));
                    #endif

                    #ifdef SixToThree
                    set_width_bitmap(&best_read63_bitmap,i,get_width_bitmap(R63bitmap,i));
                    #endif
                } else if (is_reg_bitmap(best_bitmap, i, IA64_READ)) {
                    //if our current state is READ, then ALL children must be READ also. Or CLEAR.
                     
                    if (is_reg_bitmap(bitmap, i, IA64_READ)) {
                        #ifdef STRATEGY_WIDTH
                        if (get_width_bitmap(widthmap,i) < get_width_bitmap(best_width_bitmap,i) )
                        {
                            if (get_width_bitmap(best_width_bitmap,i) != 9)
                                dprintf("find smaller width %lx,%d,%d\n",f->get_base_addr(),get_width_bitmap(best_width_bitmap,i),get_width_bitmap(widthmap,i));
                            set_width_bitmap(&best_width_bitmap,i,get_width_bitmap(widthmap,i));
                        }
                        #endif

                        #ifdef SixToThree

                        if (get_width_bitmap(R63bitmap,i) > get_width_bitmap(best_read63_bitmap,i))
                        {
                            set_width_bitmap(&best_read63_bitmap,i,0x9);
                        }

                        #endif
                       
                    } else if (is_reg_bitmap(bitmap, i, IA64_WRITE)) {
                        set_reg_bitmap(&best_bitmap, i, IA64_WRITE);
                        set_width_bitmap(&best_width_bitmap,i,0x9);
                        set_width_bitmap(&best_read63_bitmap,i,0x9);
                    } else if (is_reg_bitmap(bitmap, i, IA64_RW)) {
                        set_reg_bitmap(&best_bitmap, i, IA64_RW);
                        set_width_bitmap(&best_width_bitmap,i,0x9);
                        set_width_bitmap(&best_read63_bitmap,i,0x9);
                    } else if (is_reg_bitmap(bitmap, i, IA64_CLEAR)) {
                        set_reg_bitmap(&best_bitmap, i, IA64_CLEAR);
                        set_width_bitmap(&best_width_bitmap,i,0x9);
                        set_width_bitmap(&best_read63_bitmap,i,0x9);
                    }
                } else if (is_reg_bitmap(best_bitmap, i, IA64_CLEAR)) {
                    //if our current state CLEAR, we can become WRITE 
                    if (is_reg_bitmap(bitmap, i, IA64_WRITE)) {
                        set_reg_bitmap(&best_bitmap, i, IA64_WRITE);
                        set_width_bitmap(&best_width_bitmap,i,0x9);
                        set_width_bitmap(&best_read63_bitmap,i,0x9);
                    } else if (is_reg_bitmap(bitmap, i, IA64_RW)) {
                        set_reg_bitmap(&best_bitmap, i, IA64_RW);
                        set_width_bitmap(&best_width_bitmap,i,0x9);
                        set_width_bitmap(&best_read63_bitmap,i,0x9);
                    }
                }
#else 
                if (is_reg_bitmap(best_bitmap, i, 0x3)) {
                    set_reg_bitmap(&best_bitmap, i, get_reg_bitmap(bitmap, i));
                    #ifdef STRATEGY_WIDTH
                    set_width_bitmap(&best_width_bitmap,i,get_width_bitmap(widthmap,i));
                    #endif

                    #ifdef SixToThree
                    set_width_bitmap(&best_read63_bitmap,i,get_width_bitmap(R63bitmap,i));
                    #endif
                } else if (is_reg_bitmap(best_bitmap, i, IA64_WRITE) ||
                           is_reg_bitmap(best_bitmap, i, IA64_RW) ||
                           is_reg_bitmap(best_bitmap, i, IA64_CLEAR)) {

                    if (is_reg_bitmap(bitmap, i, IA64_READ)) {
                        set_reg_bitmap(&best_bitmap, i, IA64_READ);
                        #ifdef STRATEGY_WIDTH
                        set_width_bitmap(&best_width_bitmap,i,get_width_bitmap(widthmap,i));
                        #endif

                        #ifdef SixToThree
                        set_width_bitmap(&best_read63_bitmap,i,get_width_bitmap(R63bitmap,i));
                        #endif
                    } else if(is_reg_bitmap(bitmap, i, IA64_WRITE)) {
                        /* ... */
                    } else if (is_reg_bitmap(bitmap, i, IA64_RW)) {
                        /* ... */
                        set_reg_bitmap(&best_bitmap, i, IA64_READ);
                        #ifdef STRATEGY_WIDTH
                        set_width_bitmap(&best_width_bitmap,i,get_width_bitmap(widthmap,i));
                        #endif

                        #ifdef SixToThree
                        set_width_bitmap(&best_read63_bitmap,i,get_width_bitmap(R63bitmap,i));
                        #endif

                    } else if (is_reg_bitmap(bitmap, i, IA64_CLEAR)) {
                        /* ... */
                    }
                }
#endif 




            }
        }
        ddprintf("[ft]%s comb_bitmap = %s\n", blanks.c_str(), bm_tostring(best_bitmap).c_str());

        #ifdef STRATEGY_WIDTH
        if (edges_followed == 0) {
            ddprintf("[ft]%s No edges followed\n", blanks.c_str());
        } 
        else {
            /*uint32_t best_width_bitmap = 0xffffff;
            for (auto it  = reg_widths.begin(); 
                    it != reg_widths.end();
                    it++) {
                uint32_t bitmap_width = *it;
                dprintf("bitmap width %x\n",bitmap_width);
                for (int i = 0; i < IA64_ARGS; i++)
                {
                    if (get_width_bitmap(bitmap_width,i) < get_width_bitmap(best_width_bitmap,i) && get_width_bitmap(bitmap_width,i)!= 0)
                    {
                        //best_width_bitmap = bitmap_width;
                        set_width_bitmap(&best_width_bitmap,i,get_width_bitmap(bitmap_width,i));
                    }
                }

            }*/
        
            //width_bitmap = best_width_bitmap;
            ddprintf("width bitmap %lx\n",width_bitmap);
            ddprintf("best width bitmap final %lx\n",best_width_bitmap);
            
            for (int i = 0; i < IA64_ARGS; i++)
            {
                /*if (is_Dcall)
                {
                    if (get_width_bitmap(best_width_bitmap,i) != 9 && get_width_bitmap(width_bitmap,i)==9)
                    {
                        set_width_bitmap(&width_bitmap,i,get_width_bitmap(best_width_bitmap,i));
                    }
                }*/
                //else{
                if (is_reg_bitmap(reg_bitmap, i, IA64_CLEAR))
                {
                    //if (get_width_bitmap(best_width_bitmap,i) < get_width_bitmap(width_bitmap,i))
                        set_width_bitmap(&width_bitmap,i,get_width_bitmap(best_width_bitmap,i));
                
                        set_width_bitmap(&read63_bitmap,i,get_width_bitmap(best_read63_bitmap,i));
                }
                else if (is_reg_bitmap(reg_bitmap, i, IA64_READ))
                {
                    if (get_width_bitmap(best_width_bitmap,i) < get_width_bitmap(width_bitmap,i))
                    {
                        if (get_width_bitmap(width_bitmap,i) != 9)
                            dprintf("find smaller width %lx,%d,%d\n",f->get_base_addr(),get_width_bitmap(best_width_bitmap,i),get_width_bitmap(width_bitmap,i));
                        set_width_bitmap(&width_bitmap,i,get_width_bitmap(best_width_bitmap,i));
                    }
                    if (get_width_bitmap(best_read63_bitmap,i) < get_width_bitmap(read63_bitmap,i))
                        set_width_bitmap(&read63_bitmap,i,0x9);
                }

            }
                
        }

        #endif
    
        /* combine */
        for (int i = 0; i < IA64_ARGS; i++) {
            if (is_reg_bitmap(reg_bitmap, i, IA64_CLEAR)) {
                set_reg_bitmap(&reg_bitmap, i, get_reg_bitmap(best_bitmap,i));
            }
        }
        ddprintf("[ft]%s updt_bitmap = %s\n", blanks.c_str(), bm_tostring(reg_bitmap).c_str());
    }

    ddprintf("[ft]%s Processed all edges, returning our best bitmap (%x)\n", blanks.c_str(), reg_bitmap);
    goto ft_debug_return;
    /*std::vector<uint32_t> info_3;
    info_3.push_back(reg_bitmap);
    info_3.push_back(width_bitmap);

    return info_3;*/
    /*std::vector<uint16_t> info_3;
    info_3.push_back(reg_bitmap);
    for (int i=0; i< IA64_ARGS;i++)
    {
        info_3.push_back((*reg_width)[i]);
    }
    
    //return reg_bitmap;
    
    return info_3;*/

ft_debug_return:
    ddprintf("[ft]%s ", blanks.c_str());
    for (auto rit  = argcount_analyzed_blocks.rbegin(); 
              rit != argcount_analyzed_blocks.rend();
              rit++) {
        ArmsBasicBlock* analyzed_block = *rit;
        ddprintf("%p <- ", (void *) analyzed_block->get_start_address());
    }
    ddprintf("(%x)\n",reg_bitmap);

    ddprintf("best width bitmap %lx\n",width_bitmap);
    ddprintf("best read63 bitmap %lx\n",read63_bitmap);

    //return reg_bitmap;
    //info.reg_bitmap = reg_bitmap;
    //info.reg_width_vector = *reg_width;
    std::vector<uint32_t> info;
    info.push_back(reg_bitmap);
    info.push_back(width_bitmap);
    info.push_back(read63_bitmap);
    /*for (int i= 0; i< IA64_ARGS;i++)
    {
        //dprintf("widht info %d\n",reg_widths[i]);
        //info.push_back(reg_widths[i]);
        dprintf("widht info %d\n",(*reg_width)[i]);
        info.push_back((*reg_width)[i]);
    }*/
    ddprintf("reg info %d\n",info[0]);

    return info;
}





bool ArmsLiveness::getForwardLiveness(ArmsFunction *f,
                                     ArmsBasicBlock *bb) {   

    ddprintf("[rec] Looking at block %p\n", (void *)bb->get_start_address());
    ddprintf("[rec]   Register status: ");

    bool done = true;
    /* update the argc_registers with information from the current block */
    /* except if this block is vararg-related and responsible for writing
     * the variadiac arguments to the stack, we stop here. 
     * The problem is that if we're in function F1, and we call variadic
     * function F2 with 2 variaric arguments, then F2 will still write a the
     * other arguments to the stack (and thus reads those arguments). This
     * will result in false conclusions on the read-state of these registers.
     */
    if (bb->is_vararg_mark()) {
        /* just stop here */
        for (int i = 0; i < IA64_ARGS; i++) {
            if (argc_registers[i] == IA64_CLEAR) {
                argc_registers[i] = IA64_WRITE;
            }
            ddprintf("%d ", argc_registers[i]);
        }
        ddprintf(" (vararg-mark)\n");
    } else {

        for (int i = 0; i < IA64_ARGS; i++) {
            if (argc_registers[i] == IA64_CLEAR) {
                argc_registers[i] = rw_registers[i].getState(bb);
                /* added by yanlin */
                //int width = width_registers[i].getWidth_callee(bb);
                //dprintf("%d width ", width);
                if (argc_registers[i] == IA64_CLEAR) done = false;
            }
            ddprintf("%d ",argc_registers[i]);
            
        }
        ddprintf("\n");
    }

    argc_analyzed_blocks.insert(bb);


    /* we can stop once we reach the point that we have a state for all registers. */
    if (done) return true;
    /* this of course should be improved by keeping track of all possible subpaths and then select
     * the path for which we get the most read before writes */


    ArmsBasicBlock *fallthrough_bb = NULL;

    /* we need to continue discovering this branch, if possible */
    /* TODO. This code is very similar to the one where we parse blocks to get
     * the information in the first place. Maybe we can easily merge this.
     * That could infect our varargs detection though.
     */
    for(size_t i = 0; i < bb->outgoing_edge_count(); i++) {
        ArmsEdge *edge = bb->get_outgoing_edge(i);
        ArmsBasicBlock *next_bb;
        
        ddprintf("[rec] edge: %lu/%lu\n",i+1,bb->outgoing_edge_count());


        if (edge->is_return()) {
            /* We won't follow return edges. Instead, when we discover a direct
             * call, we mark it's fallthrough basic block as additional edge target. That way, 
             * if we run into a direct call, we always fall back to its return.
             * Additionally, this ensures that we won't follow return edges for the
             * actual function that we are analyzing.
             */
            ddprintf("[rec]  > Not following return edge\n");
            continue;
        } else if (edge->is_direct_call()) {
            ddprintf("[rec]  > Following direct call, adding fallthrough bb as additional block that we should analyze\n");
           
            /* some direct calls never return, in which case we do not look at
             * the fallthrough */
            if (edge->target() != NULL &&
                edge->target()->get_function() != NULL &&
                (edge->target()->get_function()->get_name() == "_EXIT" ||
                 edge->target()->get_function()->get_name() == "_exit" ||
                 edge->target()->get_function()->get_name() == "__stack_chk_fail") 
                 ) {
                ddprintf("[rec]  > Call to _EXIT, not looking at fallthrough bb\n");
                continue;
            } else {
                next_bb = edge->target();
                fallthrough_bb = bb->get_fallthrough_bb();
            }
            if (next_bb != NULL)        ddprintf("[rec] next_bb: %p\n", (void *) next_bb->get_start_address());
            if (fallthrough_bb != NULL) ddprintf("[rec] fallthr: %p\n", (void *)fallthrough_bb->get_start_address());
        } else if(edge->is_indirect_call()) {
            /* We cannot follow indirect calls. We can not increase our
             * knowledge any further at this point: the target may read argument
             * registers that are passed to us without them being read before
             * this point.
             * */
            ddprintf("[rec]  > Not following indirect call edge, we are done\n");
            /* TODO can't we just return here directly? */
            continue;
        } else {
            ddprintf("[rec]  > Getting target of edge\n");
            next_bb = edge->target();
            
        }
        
        if (next_bb == NULL) {
            ddprintf("[rec]  > next bb does not exist\n");
            continue;
        }
        if (next_bb->is_entry_block() && !edge->is_interprocedural())
        {
            continue;
        }

        if (fallthrough_bb != NULL) {
            if (edge->is_direct_call() && isNop(fallthrough_bb)) {
                ddprintf("[rec]  > fallthrough is nop while last edge was a direct call. Assuming non-returning\n");
                //fallthrough_bb = NULL;
            } else if (edge->is_direct_call() && fallthrough_bb->is_entry_block()) {
                ddprintf("[rec]  > fallthrough is entry block while last edge was a direct call. Assuming non-returning\n");
                fallthrough_bb = NULL;
            }
        }

        if (argc_analyzed_blocks.find(next_bb) != argc_analyzed_blocks.end()) {
            ddprintf("[rec]  > next bb is already analyzed\n");
            continue;

            /* TODO. This is not completely ok. We should actualy continue
             * analysis if the path found is a 'better' one. Depending on our
             * results, we may have to implement this....
             */
        }
        
        /* this is also import for varargs... */
        ddprintf("next bb is entry block? %d\n", next_bb->is_entry_block());
        if (edge->is_interprocedural() && next_bb->is_entry_block()) {
            /* we are making a function call. Maybe we already completed
             * analysis for this function. */
            ArmsFunction *callee = next_bb->get_function();
            ddprintf("callee is exactly one? %p\n", callee);
            /* even if it is one, we should search all callees. then pick the callee for which it's
             * starting basic block equals this basic block and match the argcount.
             */

            if (callee && callee->get_argcount() != -1) {
                ddprintf("this callee is analyzed\n");
                /* yes, we analyzed this one */

                if (callee->get_argcount() == 0) {
                    ddprintf("the parameter count of this callee is 0\n");
                    // nothing to do
                } else {
                    ddprintf("the parameter count of this callee is %d\n",callee->get_argcount());
                    // revised by yanlin
                    for ( int i = 0; i< callee->get_argcount(); i++)
                    {
                        if (argc_registers[i] == IA64_CLEAR)
                            argc_registers[i] = IA64_READ;
                    }
                    // original
                    //if (argc_registers[callee->get_argcount()-1] == IA64_CLEAR)
                        //argc_registers[callee->get_argcount()-1] = IA64_READ;
                }

                continue;
            }
        } 
        //dprintf("Looking at next block %p\n", (void *)next_bb->get_start_address());
        if (this->getForwardLiveness(f, next_bb)) return true;
        
        
        /* do we still have a fallback to analyze perhaps? */
        if (fallthrough_bb == NULL) {
            ddprintf("[rec]  > no fallthrough\n");
            continue;
        } 
        if (argc_analyzed_blocks.find(fallthrough_bb) != argc_analyzed_blocks.end()) {
            ddprintf("[rec]  > fallthrough already analyzed\n");
            continue;
        }

        if (this->getForwardLiveness(f, fallthrough_bb)) return true;

    }

    return false;
}

//added by yanlin
#ifdef TRACE_CALLER
void ArmsRegister::setStateCaller(ArmsBasicBlock *block, unsigned long offset, StateType state) {
//  dprintf("setState(%p, %p, %d) (this: %p)\n", block, (void *) offset, state, this);

    if ((block_list_caller[block][offset] == IA64_READ  && state == IA64_WRITE) || 
        (block_list_caller[block][offset] == IA64_WRITE && state == IA64_READ)) {
        block_list_caller[block][offset] = IA64_RW;
    } else {
        block_list_caller[block][offset] = state;
    }
    
}

std::map <unsigned long, StateType> ArmsRegister::getStateCaller(ArmsBasicBlock *block) {
    StateType reg_state = IA64_CLEAR; /* register is untouched by default */
    std::map <unsigned long, StateType> r;
    if (block_list_caller.count(block) != 1) 
    {
        r[-1] = reg_state;
        return r;
    }

    
    /* loop over all recorded states for this block */
    for (state_it_type it  = block_list_caller[block].begin(); 
                       it != block_list_caller[block].end(); 
                       it++) {
        unsigned long insn_offset = it->first;  /* instruction offset */
        reg_state = it->second;

        /* stop once the first state change was observed */
        /*if (reg_state == IA64_WRITE) 
        {
            r[insn_offset] = reg_state;
            break;
        }*/
        r[insn_offset] = reg_state;
    }

    return r;
}

void ArmsLiveness::parse_register_caller(RegisterAST::Ptr reg, 
                                  ArmsBasicBlock *bb, unsigned long offset, StateType state) {
    
    int reg_index = get_reg_index(reg);
   
    if (reg_index < 0) return;
    
    ddprintf("              : (%d): %s -> %s\n", reg_index, 
                         get_register_name(reg_index).c_str(), 
                    ArmsRegister::getStateName(state).c_str());
    rw_registers[reg_index].setStateCaller(bb, offset, state);  
}

void ArmsLiveness::parse_register_set_caller(std::set<RegisterAST::Ptr> register_set, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state) {
 
    for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                              it != register_set.end(); 
                                              it++) {
        RegisterAST::Ptr reg = *it;
        int  reg_value = reg->getID().val();
        parse_register_caller(reg, bb, offset, state);
    }
        
}

void ArmsLiveness::parse_caller_instruction(Instruction::Ptr iptr,
                                     ArmsBasicBlock *bb, unsigned long offset)
{
    if (!iptr->isLegalInsn()) {
        ddprintf("      %p: [ILLEGAL INSTRUCTION]\n", (void *) offset);
        bb->set_disas_err((void*) offset);
        return;
    }
    ddprintf("      %p: %s\n", (void *) offset, iptr->format(0).c_str());

    
    /*RegisterAST::Ptr reg = is_dereference(iptr);
    if (reg != NULL) {
        int reg_index = get_reg_index(reg);
        if (reg_index >= 0) {
            dprintf("setting deref\n");
            rw_registers[reg_index].setDeref(bb, offset);
        }
    }*/

    ins_length[offset] = iptr->size();

    if (iptr->size() == 2 && iptr->rawByte(0) == 0xF3 && iptr->rawByte(1) == 0x90) {
        ddprintf("                PAUSE\n");
        return;
    }
    if (iptr->size() == 2 && iptr->rawByte(0) == 0x0F && iptr->rawByte(1) == 0xA2) {
        ddprintf("                CPUID\n");
        return;
    }
    /* TODO: for us, syscalls are not indirect calls. we should modify the arms
     * interface so that it does not add those edges in the first place */
    /*if (iptr->size() == 2 && iptr->rawByte(0) == 0x0F && iptr->rawByte(1) == 0x05) {
        dprintf("                SYSCALL\n");
        bb->set_syscall();
    }*/
    /* TODO:
        if (iptr->size() == 2 && iptr->rawByte(0) == 0x0f && iptr->rawByte(1) == 0x0b) {
            dprintf("                UD2\n");
        }
    */

    std::set<RegisterAST::Ptr> register_set;

    if (!isNop(iptr)) iptr->getReadSet(register_set);
    parse_register_set_caller(register_set, bb, offset, IA64_READ);
    register_set.clear();

    if (!isNop(iptr)) iptr->getWriteSet(register_set);
    parse_register_set_caller(register_set, bb, offset, IA64_WRITE);
    register_set.clear();
}

void ArmsLiveness::parse_caller(ArmsBasicBlock *bb)
{
   ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
    if (!pblock) return; // TODO

    /* Parse the instructions of this basic block */
    ParseAPI::Block::Insns insns;
    pblock->getInsns(insns);
    for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                          it != insns.end(); 
                                          it++) {
        /* it->first:  offset
         * it->second: instruction */
        parse_caller_instruction(it->second, bb, it->first);
    }
}

bool ArmsRegister::writtenInCaller(ArmsBasicBlock *block) {
    StateType reg_state;

    for (state_it_type it  = block_list_caller[block].begin();
                       it != block_list_caller[block].end();
                       it++) {
        unsigned long insn_offset = it->first;
        reg_state = it->second;

        if (reg_state == IA64_WRITE) 
        {
            return true;
        }
    }

    return false;
}

bool ArmsRegister::readInCaller(ArmsBasicBlock *block)
{
    StateType reg_state;

    for (state_it_type it  = block_list_caller[block].begin();
                       it != block_list_caller[block].end();
                       it++) {
        unsigned long insn_offset = it->first;
        reg_state = it->second;

        if (reg_state == IA64_RW || reg_state == IA64_READ) 
        {
            ddprintf("read register\n");
            return true;
        }
    }

    return false;
}


int ArmsLiveness::traceCaller(ArmsBasicBlock *bb)
{
    ddprintf("Enter traceCaller\n");
    int dcallerArg = 0;
    int callerArg = 0;
    for (size_t i = 0; i < bb->incoming_edge_count(); i++)
    {
        ArmsEdge *edge = bb->get_incoming_edge(i);
        ArmsBasicBlock *prev_bb;
        // direct call
        if (edge->is_direct_call())
        {
            //get the caller basic block
            prev_bb = edge->source();
            if (prev_bb != NULL) 
            {
                ddprintf("analysis caller %lx\n",prev_bb->get_start_address());
                int j = 0;
                //if (!is_analyzed(prev_bb))
                {
                    ddprintf("check how many arguments are set\n");
                    parse_caller(prev_bb);
                    for ( j = 0; j < IA64_ARGS; j++)
                    {
                        if (rw_registers[j].writtenInCaller(prev_bb))
                        {
                            
                            ddprintf("write register %d\n",j);
                            if (rw_registers[j].readInCaller(prev_bb))
                            {
                                ddprintf("read register %d\n",j);
                                return j;
                            }
                        }
                        else
                        {
                            break;
                        }
                        
                       
                    }
                    callerArg = j;
                }
                
                ddprintf("number of argument is %d\n",callerArg);
                if (callerArg > dcallerArg)
                {
                    dcallerArg = callerArg;
                }
            }
        }
    }
    ddprintf("the final number of argument is %d\n",dcallerArg);
    return dcallerArg;
   


}
#endif
//end of yanlin

/* only perform the variadic detection. We need to have exclusive results on this before we run 
 * func-arg detection */
int ArmsLiveness::get_vararg_count(ArmsFunction *f) {
    /* Only if this function was analyzed */
    if (function_blocks.count(f) == 0) {
        return -1;
    }
    
    int argcount = is_variadic(f);
    if (argcount) {
        f->set_variadic();
        f->set_argcount(argcount);
        ddprintf("Detected variadic function with %d fixed arguments: %s\n", 
                argcount, f->get_name().c_str());
        return argcount;
    }

    return -1;
}

int ArmsLiveness::get_arg_count(ArmsFunction *f) {
    /* Only if this function was analyzed */
    if (function_blocks.count(f) == 0) {
        return -1;
    }


    /* before doing anything else, search for writes on RAX to get the status for return value use */
    ddprintf("\n=== Starting retuse analysis for function %s ===\n", f->get_name().c_str());

    /* Start with the exit blocks of this function. */
    std::vector<ArmsBasicBlock*> exit_blocks;
    exit_blocks.assign(f->get_exit_points()->begin(), f->get_exit_points()->end());

    /* Recursively analyze each block of the function starting from the entry blocks */
    /* This is a depth first search */

    std::vector<ArmsBasicBlock *> callee_retuse_analyzed_blocks;
   
    f->set_write_rax(true);
    ddprintf("-> number of exit blocks: %lu\n", exit_blocks.size());
    while(exit_blocks.size() > 0) {
        callee_retuse_analyzed_blocks.clear();

        ArmsBasicBlock *bb = exit_blocks.back();
        exit_blocks.pop_back();

        /* all exit points of the callee must be the result of a path that writes rax */
        if (!getRAXwrites(f, bb, callee_retuse_analyzed_blocks)) {
            f->set_write_rax(false);
            break;
        }
    }

    ddprintf("=== Finished retuse analysis for function %s: %d ===\n\n", f->get_name().c_str(), f->get_write_rax());




    if (f->get_argcount() != -1) {
        /* this is a variadic function. not proceeding */
        return -1;
    }


    /* ASSUMING THAT This is *NOT* a variadic function */

    /* Conservative strategy:
     * - do not analyze nested function calls
     * - assume *all* parameter registers are used at some point in the function
     */

#if STRATEGY_TYPE == STRATEGY_CONSERVATIVE
    for (argcount = 0; argcount < IA64_ARGS; argcount++) {
        ddprintf("  [args] %d: %s - %s\n", argcount, get_register_name(argcount   ).c_str(), 
                                                     get_regstate_name(argcount, f).c_str());
        if (!rw_registers[argcount].isRead(function_blocks[f])) {

#if STRATEGY_OPTIONS & STRATEGY_CON_OPT_EXPECT_2ND_RETVAL
            /* RDX may be used to store a second return value. We currenly only see
             * this in vsftpd... */
            if (argcount-1 == IA64_RDX) {
   
                /* We do not have to decrease the argcount if RDX was read
                 * before a call instruction */
                std::vector<ArmsBasicBlock *> blocks;
                for (std::vector<ArmsBasicBlock *>::iterator it  = function_blocks[f].begin();
                                                             it != function_blocks[f].end();
                                                             it++) {
                    ArmsBasicBlock *bb = *it;
                    blocks.push_back(bb);
                    if (bb->outgoing_contains_call()) break;
                }

                ArmsBasicBlock *rdx_read_block = rw_registers[IA64_RDX].getReadBB(function_blocks[f]);

                if (find(blocks.begin(), blocks.end(), rdx_read_block) != blocks.end()) {
                    /* The first READ RDX instruction occurs before a call instruction. */
                } else {
                    /* The first READ RDX is after a call instruction. Without
                     * performing recursion, we must assume it was set by a child
                     * function as a second return value and thus decrement the
                     * argcount.
                     */
                    argcount--;
                }
                
            }
#endif // STRATEGY_CON_OPT_EXPECT_2ND_RETVAL
            break;
        }
    }
#elif STRATEGY_TYPE == STRATEGY_RECURSIVE
    dprintf("\n=== Starting recursive analysis for function %s ===\n", f->get_name().c_str());
       
    /* Start with the entry blocks of this function. */
    std::vector<ArmsBasicBlock*> entry_blocks;
    entry_blocks.assign(f->get_entry_points()->begin(), f->get_entry_points()->end());



    /* Recursively analyze each block of the function starting from the entry blocks */
    /* This is a depth first search */

    for (int i = 0; i < IA64_ARGS; i++) {
        argc_registers[i] = IA64_CLEAR;
    }
    argc_analyzed_blocks.clear();

    while(entry_blocks.size() > 0) {
        ArmsBasicBlock *bb = entry_blocks.back();
        entry_blocks.pop_back();


        if (argc_analyzed_blocks.find(bb) == argc_analyzed_blocks.end()) 
            getForwardLiveness(f, bb);
    }

    int argcount = 0;
    for (int i = IA64_ARGS; i >=0; i--) {
		// modified by yanlin
        //if (argc_registers[i] == IA64_READ || argc_registers[i] == IA64_RW ) {
        if (argc_registers[i] == IA64_READ){  
            argcount = i+1;
            break;
        }
    }
    ddprintf("number of parameter before tracing caller %d\n",argcount);
    //added by yanlin
    #ifdef TRACE_CALLER
    std::vector<ArmsBasicBlock*> entry_blocks_new;
    entry_blocks_new.assign(f->get_entry_points()->begin(), f->get_entry_points()->end());
    int dcallerArg = 0;
    while(entry_blocks_new.size() > 0){
        ArmsBasicBlock *bb = entry_blocks_new.back();
        entry_blocks_new.pop_back();

        int callerArg = traceCaller(bb);
        if (callerArg > dcallerArg){
            dcallerArg = callerArg;
        }
    }
    dprintf("number of argument for caller %d\n",dcallerArg);
    if (dcallerArg > argcount && dcallerArg <= 6){
        int count_final = 0;
        for (count_final = 0; count_final < dcallerArg; count_final++)
        {
            if (argc_registers[count_final] == IA64_WRITE)
            {
                break;
            }
        }
        
        ddprintf("dcallerArg large than argcount%d\n",dcallerArg);
        argcount = count_final; 
    }
    ddprintf("number of parameter %d\n",argcount);
    #endif

    ddprintf("=== Finished recursive analysis ===\n\n");

#elif STRATEGY_TYPE == STRATEGY_CONCLUSIVE
    dprintf("\n=== Starting conclusive analysis for function %s ===\n", f->get_name().c_str());

    /* Start with the entry blocks of this function. */
    std::vector<ArmsBasicBlock*> entry_blocks;
    entry_blocks.assign(f->get_entry_points()->begin(), f->get_entry_points()->end());

    /* Recursively analyze each block of the function starting from the entry blocks */
    /* This is a depth first search */

    uint16_t reg_bitmap = 0;
    for (int i = 0; i < IA64_ARGS; i++) {
        set_reg_bitmap(&reg_bitmap, i, IA64_CLEAR);
    }

    #ifdef STRATEGY_WIDTH
    for (int i = 0; i < IA64_ARGS; i++)
    {
        //function_argwidth[f][i] = 9;
        function_argwidth[f->get_base_addr()].push_back(9);
        
    }
    #endif

    #ifdef STRATEGY_WIDTH
    std::vector<uint16_t>reg_width;
    for (int i = 0; i < IA64_ARGS; i++)
    {
        reg_width.push_back(9);
    }
    #endif


    std::vector<ArmsBasicBlock *> argcount_analyzed_blocks;
    std::vector<ArmsBasicBlock *> fts;
    argcount_analyzed_blocks.clear();

    assert(entry_blocks.size() == 1);

    //
    //struct result info;
    std::vector<int> first_flag;
    for (int i = 0; i< IA64_ARGS; i++)
    {
        first_flag.push_back(1);
        FunctionR63[f->get_base_addr()][i] = 1;
        Fread64to32[f->get_base_addr()][i] = 0;
    }
    
    std::vector<uint32_t>info = getForwardLiveness2(f, entry_blocks[0],NULL, fts, argcount_analyzed_blocks,&reg_width,first_flag);

    


    //dprintf("testing vector %x\n",info[0]);
    //for (int i = 0; i< IA64_ARGS+1; i++)
    reg_bitmap = info[0];
    ddprintf("reg bitmap is %d\n",reg_bitmap);
    int argcount = 0;
    for (int i = IA64_ARGS; i >=0; i--) {
		//revised by yanlin
        if (get_reg_bitmap(reg_bitmap, i) == IA64_READ) {
            argcount = i+1;
            break;
        }
    }

    //debuging
    /*for (int i = 0; i < IA64_ARGS; i++)
    {
        dprintf("debuging width %d ", function_argwidth[f][i]);
    }
    printf("\n");*/
    
    int ReadRDX = 0;
    dprintf("=== Finished recursive analysis for function %s: %d ===\n\n", f->get_name().c_str(), argcount);
#endif
    
    /* RDX may be used to store a second return value. We currenly only see
            * this in vsftpd... */
    if (argcount-1 == IA64_RDX) {

        /* We do not have to decrease the argcount if RDX was read
            * before a call instruction */
        std::vector<ArmsBasicBlock *> blocks;
        std::vector<ArmsBasicBlock *> blocks_after_call;
        std::set<ArmsBasicBlock*> *bbs = f->get_basic_blocks();
        for (std::set<ArmsBasicBlock *>::iterator it  = bbs->begin();
                                                        it != bbs->end();
                                                        it++) {
            ArmsBasicBlock *bb = *it;
            blocks.push_back(bb);
            if (bb->outgoing_contains_inter()) 
            {
                break;
            }
            

        }
        int ret = 0;
        for (std::set<ArmsBasicBlock *>::iterator it  = bbs->begin();
                                                        it != bbs->end();
                                                        it++) {
                                        
            ArmsBasicBlock *bb = *it;
            
            if (find(blocks.begin(), blocks.end(),bb) == blocks.end())
            {
                blocks_after_call.push_back(bb);
                ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
                //if (!pblock) return; // TODO

                /* Parse the instructions of this basic block */
                ParseAPI::Block::Insns insns;
                pblock->getInsns(insns);


                for (ParseAPI::Block::Insns::iterator it  = insns.begin(); 
                                          it != insns.end(); 
                                          it++) {
                    /* it->first:  offset
                    * it->second: instruction */
                    
                    //instr = it->second;
                    std::string ins_str = (it->second)->format(0).c_str();
                    if (ins_str.find("ret") != std::string::npos || ins_str.find("jmp") != std::string::npos)
                    {
                        ret = 1;
                        //printf("basic block %lx finds ret\n",bb->get_start_address());
                        break;
                    }
                }


                if (ret)
                    break;
               
            }
        }

        //ArmsBasicBlock *rdx_read_block = rw_registers[IA64_RDX].getReadBB(*bbs);

        //if (find(blocks.begin(), blocks.end(), rdx_read_block) != blocks.end()) {
            /* The first READ RDX instruction occurs before a call instruction. */
        if (rw_registers[IA64_RDX].getState(blocks) == IA64_READ){
        
        } else {
            if (rw_registers[IA64_RDX].getState(blocks_after_call) == IA64_READ)
            {
                ReadRDX = 1;
                //ReadRDX.insert(f->get_base_addr());
                //printf("Read RDX after a call instruction %lx\n",f->get_base_addr());
                /* The first READ RDX is after a call instruction. Without
                    * performing recursion, we must assume it was set by a child
                    * function as a second return value and thus decrement the
                    * argcount.
                    */
                //argcount--;
            }
        }
        
    }
   

    ddprintf("Detected normal function with %d arguments: %s\n", argcount, f->get_name().c_str());
    
    #ifdef TRACE_CALLER
    std::vector<ArmsBasicBlock*> entry_blocks_new;
    entry_blocks_new.assign(f->get_entry_points()->begin(), f->get_entry_points()->end());
    int dcallerArg = 0;
    while(entry_blocks_new.size() > 0){
        ArmsBasicBlock *bb = entry_blocks_new.back();
        entry_blocks_new.pop_back();

        int callerArg = traceCaller(bb);
        if (callerArg > dcallerArg){
            dcallerArg = callerArg;
        }
    }
    ddprintf("number of argument for caller %d\n",dcallerArg);
    if (dcallerArg > argcount && dcallerArg <= 6){
        int count_final = 0;
        for (count_final = 0; count_final < dcallerArg; count_final++)
        {
            if (argc_registers[count_final] == IA64_WRITE)
            {
                break;
            }
        }
        
        ddprintf("dcallerArg large than argcount%d\n",dcallerArg);
        argcount = count_final; 
    }
    ddprintf("number of parameter %d\n",argcount);
    #endif


 
    #ifdef STRATEGY_WIDTH
    std::vector<uint16_t> arg_width;
    #ifdef STATISTICS
    //int Fr64to32 = 0;
    std::vector<int>Fr64to32;
    for (int i = 0; i< IA64_ARGS;i++)
    {
        Fr64to32.push_back(0);
    }
    #endif
    for (int i = 0; i < argcount; i++) {
        int width = get_width_bitmap(info[1],i);

        //int width = reg_width[i];
        //if (info)
        //if ( reg_width[i] < width)
            //width = reg_width[i];

        int f_width = width_registers[i].getWidth_callee(function_blocks[f]);

        ddprintf("f_width %d \n", f_width);
        //if (f_width > width && f_width != 9)
            //width = f_width;
        arg_width.push_back(width);

        #ifdef SixToThree
        if ( get_width_bitmap(info[2], i) == 8 && width == 8)
        {
            #ifdef STATISTICS
            Fr64to32[i] = i+1;
            //set_width_bitmap(&info[2],i,0x4);
            arg_width[i] = 0x4;
            //Fr64to32.insert(f->get_base_addr());
            #endif
            //printf("Function %s read 64 to 32 \n",f->get_name().c_str());
        }
            
        #endif 
        #ifdef secondLea
        int r = is_secondlea(f);
        if (r)
        {
            Fr64to32[r-1] = r;
             arg_width[r-1] = 0x4;
        }
        #endif
       
    }
    f->set_argwidth(arg_width);
    #endif 

    #ifdef STATISTICS
    f->set_readRDX(ReadRDX);
    f->set_Fread64to32(Fr64to32);
    #endif

    f->set_argcount(argcount);
    f->set_argbitmap(reg_bitmap);

	

    return argcount;
}

/* If the provided set of preceding_blocks contain entry_blocks for function f,
 * recursively continue searching for preceding blocks in callers of f.
 *
 * returns true if the preceding blocks contain entry blocks.
 */

#define MAX_DEPTH 10

bool follow_entry_blocks(std::set<ArmsBasicBlock *> *preceding_blocks, ArmsFunction *f, 
                         std::set<ArmsFunction   *> *processed_callers, 
                         int depth, unsigned long icall_addr) {

    /* It could happen that we end up with an entry block that has zero callers.
     * In exim with -O1, for example, there is a function dbmdb_find() that is
     * called by dbmnz_find() which is called from nowhere. We must then
     * conclude that dbmnz_find() could be the target of an indirect call itself
     * (it should have its address taken) and, as we cannot continue the live
     * analysis recursively, must conclude that we cannot determine the argcount
     * for the indirect callsite.
     *
     * We will use entry_block_left as a boolean that is true if the set of
     * preceding blocks contain an entry block with zero callers. Moreover, this
     * is only true if there is no other entry block higher up the CFG that has
     * a caller.
     */
    bool entry_block_left = true;


    std::set<ArmsBasicBlock*>* entry_blocks = f->get_entry_points(); 
    for (std::set<ArmsBasicBlock *>::iterator it  = entry_blocks->begin();
                                              it != entry_blocks->end();
                                              it++) {
        ArmsBasicBlock *entry_block = *it;
        if (preceding_blocks->count(entry_block)) {

            if (depth == 0)
                ddprintf("the proceeding of the indirect call can be the entry block %lx\n",icall_addr);
            /* Set of preceding blocks contains an entry block, look at callers */
            std::set<ArmsFunction *> callers = f->get_callers();
            

            for (std::set<ArmsFunction*>::iterator it  = callers.begin();
                                                   it != callers.end();
                                                   it++) {
                ArmsFunction *caller = *it;

                if (processed_callers->count(caller))
                    /* Already processed */
                    continue;

                ddprintf("Looking at caller %s\n", caller->get_name().c_str());
                processed_callers->insert(caller);
                entry_block->get_preceding_bbs(preceding_blocks, caller->get_basic_blocks());

                /* Recursion */
                if (depth < MAX_DEPTH) {
                    bool res = follow_entry_blocks(preceding_blocks, caller, processed_callers, depth++,icall_addr);
                    if (entry_block_left) entry_block_left = res;
                } else {
                    ddprintf("Reached maxdepth\n");
                    entry_block_left = false;
                }
            }
        } else {
            entry_block_left = false;
        }
    }

    return entry_block_left;
}

RegisterAST::Ptr ArmsLiveness::is_dereference(Instruction::Ptr iptr) {
    std::vector<Operand> operands;
    iptr->getOperands(operands);
    for (std::vector<Operand>::iterator it  = operands.begin();
                                        it != operands.end();
                                        it++) {
        Operand operand = *it;
        Expression::Ptr expr = operand.getValue();

        /* we are only interested in operands that are read */
        if (!operand.isRead()) continue;

        /* if more than two registers are used, either one may contain a
         * pointer. so we can only support operands that read one register.
         * let's assume that if we see a computation with a constant, the
         * constant is never an address. */
        std::set<RegisterAST::Ptr> register_set;
        register_set.clear();
        operand.getReadSet(register_set);
        if (register_set.size() != 1) continue; 
            
        RegisterAST::Ptr reg;
        for (std::set<RegisterAST::Ptr>::iterator it  = register_set.begin(); 
                                                  it != register_set.end(); 
                                                  it++) {
            reg = *it;
        }

        OperandType operandType;
        operand.getValue()->apply(&operandType);
        if (operandType.dereference)  {
            ddprintf("      [dereference read-operand]: %s\n", operand.format(Arch_x86_64).c_str());
            return reg;
        }
    }
    return NULL;
}

/* returns true if the provided instruction contains a computation */
bool ArmsLiveness::computation_used(Instruction::Ptr iptr) {
    std::vector<Operand> operands;
    iptr->getOperands(operands);
    for (std::vector<Operand>::iterator it  = operands.begin();
                                        it != operands.end();
                                        it++) {
        Operand operand = *it;
        Expression::Ptr expr = operand.getValue();

        OperandType operandType;
        operand.getValue()->apply(&operandType);
        if (operandType.binaryFunction) 
            return true;
    }
    return false;
}

#define ICALL_OPTIMIZATION_MIN_ARG_USE_ICALLS 10        // X below
#define ICALL_OPTIMIZATION_MIN_ARG_USE_PERCENTAGE 40    // Y below
/* Without any optimization, we found that many indirect call instructions use
 * one of the argument registers as target address, e.g., call *%rcx. In these
 * cases the used argument register limits the upper bound of the number of prepared
 * parameters for the called function (in the case of call *%rcx, a maximum of 3
 * parameters shall be provided: %rdi, %rsi and %rdx). This is a perfect means
 * to fixate the maximum number of arguments prepared at an indirect callsite.
 *
 * We also observed that without optimization, not many indirect call
 * instructions that use one of the arguments registers consist of a
 * computation. In other words, we won't see many instructions like call
 * *0x50(%rcx). However, with optimization enabled (starting from -O1 already),
 * these computations become much more common, while at the same time the number
 * of call *%<arg_register> instructions (without the use of a computation)
 * drops drastically.
 *
 * As such, we implemented a mechanism that detects whether indirect call
 * instructions are optimized or not. By default, we assume the binary is
 * optimized. However, if we see more than X occurences of indirect call
 * instructions that use an argument register, say N, we take a closer look. If,
 * for those N instructions, the percentage of instructions that contain a
 * computation is less than Y, we conclude that the binary (or at least the
 * indirect call instructions) is unoptimized and we can thus rely on above
 * information (limiting the upper bound of prepared arguments by looking at the
 * target register).
 */

/* Returns true if indirect calls are optimized */
bool ArmsLiveness::icalls_optimized(void) {

    if (opt_detector_completed) return is_optimized;

    unsigned int icalls = 0;
    unsigned int icalls_with_arg_use = 0;
    unsigned int icalls_with_arg_use_and_computation = 0;

    for (std::map<ArmsFunction *, std::set<ArmsBasicBlock *> > ::iterator ix  = icall_blocks.begin();
                                                                          ix != icall_blocks.end();
                                                                          ix++) {
        ArmsFunction *f = ix->first;
        ddprintf("Looking at f: %s\n", f->get_name().c_str());

        for (std::set<ArmsBasicBlock *>::iterator it  = icall_blocks[f].begin();
                                                  it != icall_blocks[f].end();
                                                  it++, icalls++) {
            ArmsBasicBlock *block = *it;

            /* Get the indirect call instruction */
            unsigned long icall_addr = block->get_last_insn_address();
            ddprintf("- indirect call at %p\n", (void *) icall_addr);

            ParseAPI::Block *pblock = (ParseAPI::Block *) block->get_parse_block();
            Instruction::Ptr iptr = pblock->getInsn( icall_addr );

            /* Get the first argument register that is used by this instruction (if any) */
            int arg_register = getFirstReadArgRegister(block, icall_addr);


            /* If any... */
            if (arg_register != IA64_ARGS) {
                /* ... determine whether a computation was used. If more than
                 * ICALL_OPTIMIZATION percent of these instructions contain a
                 * computation, we conclude that the indirect call instructions are
                 * optimzed.
                 */
                if (computation_used(iptr))
                    icalls_with_arg_use_and_computation++;

                icalls_with_arg_use++;
            }
        }
    }

    opt_detector_completed = true;

    ddprintf("[icall-optimization-detection] #icalls:                       %3u\n", icalls);
    ddprintf("[icall-optimization-detection] #icalls arg use:               %3u\n", icalls_with_arg_use);
    ddprintf("[icall-optimization-detection] #icalls arg use + computation: %3u\n", icalls_with_arg_use_and_computation);
    if (icalls_with_arg_use > ICALL_OPTIMIZATION_MIN_ARG_USE_ICALLS) {
        float percentage = (float) icalls_with_arg_use_and_computation / (float) icalls_with_arg_use * 100.0;
        ddprintf("[icall-optimization-detection] percentage:                    %5.2f\n", percentage);
        if (percentage < ICALL_OPTIMIZATION_MIN_ARG_USE_PERCENTAGE)
            is_optimized = false;
    }

    ddprintf("[icall-optimization-detection] icalls optimized? %d\n", is_optimized);

    return is_optimized;
}

#ifdef PARSE_DATA_SECTION
int ArmsLiveness::icall_statis(std::vector<ArmsBasicBlock *> blocks, address_t icall_addr, std::vector<uint16_t> reg_width, int argcount)
{
    std::vector<ArmsBasicBlock *>::iterator it;

    std::map<unsigned long, int>::iterator itr1;
    std::map<ArmsBasicBlock *, std::map<unsigned long, int> >::iterator itr2;
    

    for (it = blocks.begin(); it != blocks.end();it++)
    {
        ArmsBasicBlock *bb = *it;
       
        ParseAPI::Block *pblock = (ParseAPI::Block *) bb->get_parse_block();
        if (!pblock) return 0; // TODO

        /* Parse the instructions of this basic block */
        ParseAPI::Block::Insns insns;
        pblock->getInsns(insns);

        for (ParseAPI::Block::Insns::iterator itt  = insns.begin(); 
                                          itt != insns.end(); 
                                          itt++) {
            /* itt->first:  offset
            * itt->second: instruction */
            
            Instruction::Ptr iptr= itt->second;
            
            if (insn_constant.find(bb) != insn_constant.end())
            {
                std::map<unsigned long, int> offset_insn = insn_constant[bb];
                if ( offset_insn.find(itt->first) != offset_insn.end()) 
                {
                    //dprintf("constant insn\n");
                    std::set<RegisterAST::Ptr> register_set;

                    if (!isNop(iptr)) iptr->getWriteSet(register_set);

                    for (std::set<RegisterAST::Ptr>::iterator itr  = register_set.begin(); 
                                                itr != register_set.end(); 
                                                itr++) {

                        RegisterAST::Ptr reg = *itr;
                        int reg_index = get_reg_index(reg);
                        if ( reg_index < argcount && reg_width[reg_index] == 4)
                        {
                            if (icall_with_constant.find(icall_addr) == icall_with_constant.end() )
                                icall_with_constant.insert(icall_addr);
                           return 0;   
                        }
                    }
                }   
            }  
        }
    }
    return 0;
}
#endif

int ArmsLiveness::get_icallsites(ArmsFunction *f) {
    /* Assumes that get_arg_count() was called for all functions.
     *
     * TODO We should build one main function that accepts the CFG and then
     * performs all the analysis for us.
     */

    
    int i = 0;
    for (std::set<ArmsBasicBlock *>::iterator it  = icall_blocks[f].begin();
                                              it != icall_blocks[f].end();
                                              it++, i++) {
        ArmsBasicBlock *block = *it;
        unsigned long icall_addr = block->get_last_insn_address();
        dprintf("\n%s() got icall in basic block: %p\n", f->get_name().c_str(), (void*)block->get_start_address());

        #ifdef SixToThree
        std::vector<int>first_write;
        for ( int j = 0; j < IA64_ARGS; j++)
        {
            BBR36[block][j] = 0;
            BBR13[block][j] = 0;
            BBConstant[block][j] = 0;
            first_write.push_back(1);
            icall_constant[icall_addr][j] = 0;
            icall_R36[icall_addr][j] = 0;
            icall_R13[icall_addr][j] = 0;

            #ifdef CHECK_XOR
            BBicallXor[block][j] = 0; 
            #endif
            
        }
        
        #endif 
        icall_in_wrapper[icall_addr] = 0;
        icall_bet_info[icall_addr] = 0;

        std::vector<ArmsBasicBlock *> retuse_analyzed_blocks;
        std::vector<ArmsBasicBlock *> retuse_fts;

        /* search for reads on rax first */
        if (block->get_fallthrough_bb() == NULL) {
            // tail icall optimization? assume whatever */
            block->set_read_rax(false);
        } else if (getRAXreads(f, block->get_fallthrough_bb(), retuse_fts, retuse_analyzed_blocks)) {
            block->set_read_rax(true);
            ddprintf("!! icallsite %s.%d (%p) reads RAX !!\n", f->get_name().c_str(), i, (void *)block->get_last_insn_address());
        } else {
            block->set_read_rax(false);
        }

        //added by yanlin
        if (REGreads(f, block->get_fallthrough_bb(),retuse_fts, retuse_analyzed_blocks))
            ddprintf("!! indirect callsite %s.%d (%p) reads REG !!\n", f->get_name().c_str(), i, (void *)block->get_last_insn_address());

        
        uint16_t reg_bitmap = 0;
        uint32_t width_bitmap = 0xffffff;
        for (int i = 0; i < IA64_ARGS; i++) {
            set_reg_bitmap(&reg_bitmap, i, IA64_READ);
            set_width_bitmap(&width_bitmap, i, 0);

        }
        std::vector<ArmsBasicBlock *> callsite_analyzed_blocks;
        callsite_analyzed_blocks.clear();
        std::vector<uint32_t> result;
        #ifdef BETWEEN_CALL
        if (ret_blocks[f].find(block) != ret_blocks[f].end()){
            for (int i = 0; i < IA64_ARGS; i++) {
                if (is_reg_bitmap(reg_bitmap, i, IA64_READ)) {
                    if (rw_registers[i].writtenInBlock(block)) {
                        set_reg_bitmap(&reg_bitmap, i, IA64_WRITE);
                        #ifdef STRATEGY_WIDTH
                        int width = width_registers[i].getWidth_callsite(block);
                        set_width_bitmap(&width_bitmap,i,width);
                        #endif
                    } 
                }
            
            }
            result.push_back(reg_bitmap);
            result.push_back(width_bitmap);
        }
        else{
            result = getBackwardLiveness(f, block, callsite_analyzed_blocks,0,icall_addr,first_write);
            reg_bitmap = result[0];
        }
        #else
        result = getBackwardLiveness(f, block, callsite_analyzed_blocks,0,icall_addr,first_write);
        reg_bitmap = result[0];
        #endif
        ddprintf("finished backward analysis\n");

        //testing, added by yanlin
        /*{
            
            if (ret_blocks[f].find(block) != ret_blocks[f].end())
            {
                if (block->incoming_edge_count() == 0)
                {
                    //block->set_icall_bet(0);
                    //printf("One entry %lx, %lu\n",block->get_start_address(),block->incoming_edge_count());
                }
                else
                {
                    //block->set_icall_bet(1);
                    icall_bet_info[icall_addr] = 1;
                    ddprintf("More than one entry %lx, %lu\n",block->get_start_address(),block->incoming_edge_count());
                }
            }
            
        }*/

        //end of testing

        int argcount = 6;
        for (int i = 0; i < IA64_ARGS; i++) {
            if (get_reg_bitmap(reg_bitmap, i) != IA64_WRITE) {
                argcount = i;
                break;
            }
        }
                

        int max_arguments = argcount;
        int min_arguments = argcount;

        if (!icalls_optimized()) max_arguments = getFirstReadArgRegister(block, icall_addr);

        #ifdef STRATEGY_WIDTH
        std::vector<uint16_t> arg_width;
        width_bitmap =result[1];
        std::vector<int>  icall_pointer;
        std::vector<int>  icall_imm ;
        //std::set<address_t> icall_imm;
        std::vector<int>  icall36;
        std::vector<int>  icall13;
        std::vector<int>  icallxor;
        for ( int i =0; i < argcount; i++)
        {
            //int width = width_registers[i].getWidth_callsite(callsite_analyzed_blocks);
            
            int width = get_width_bitmap(width_bitmap,i);
            
            //printf("callsite      %s: %d\n", get_register_name(i).c_str(), width);
            if (width == 0)
            {
                width = 8;
            }
            arg_width.push_back(width);

            #ifdef STATISTICS

            icall_pointer.push_back(0);
            icall_imm.push_back(0);
            icall13.push_back(0);
            icall36.push_back(0);
            icallxor.push_back(0);

            #ifdef CHECK_XOR
            if (icall_xor.find(icall_addr) != icall_xor.end() && width == 4)
            {
                int is_xor = icall_xor[icall_addr][i];
                if (is_xor)
                {
                    icallxor[i] = i+1;
                    #ifdef xor_policy
                    set_width_bitmap(&width_bitmap,i,0x8);
                    arg_width[i] = 0x8;
                    
                    #endif
                }
            }
            #endif



            if (icall_constant.find(icall_addr) != icall_constant.end())
            {
                int is_constant = icall_constant[icall_addr][i];
                if (is_constant)
                {
                    
                    #ifdef constant_policy
                    set_width_bitmap(&width_bitmap,i,0x8);
                    arg_width[i] = 0x8;
                    #endif
                    if (is_constant == 1)
                        icall_pointer[i]=i+1;
                    else if (is_constant == 2)
                        icall_imm[i]=i+1;
                }
            }

            if (icall_R36.find(icall_addr) != icall_R36.end())
            {
                if (icall_R36[icall_addr][i])
                    icall36[i]=i+1;
            }    
            if (icall_R13.find(icall_addr) != icall_R13.end())
            {
                if (icall_R13[icall_addr][i])
                    icall13[i]=i+1;
            }
            
            #endif


        }
        ddprintf("finished statistic reults setting\n");
        /*#ifdef STATISTICS
        icall_statis(callsite_analyzed_blocks, icall_addr, arg_width, argcount);
        #endif*/

        #endif


#if 0 

        /* Get the indirect call instruction */
        ParseAPI::Block *pblock = (ParseAPI::Block *) block->get_parse_block();
        Instruction::Ptr iptr = pblock->getInsn( icall_addr );
        
        dprintf("                indirect call instruction at: %p - %s\n", (void *)icall_addr, iptr->format(0).c_str());
  
//#endif
        //int min_arguments = 0;
        //int max_arguments = IA64_ARGS;


        /* Without optimization, we can assume that if one of the argument
         * registers holds the target of the indirect call instruction, then the
         * previous argument must, at best, be the last argument that the callee
         * accepts. In other words, if we see a call *rdx, we assume that the
         * target accepts at most 3 arguments (passed in rsi, rdi and rcx).
         *
         * Of course, this does not always have to be the case. Applying
         * optimization may result in special indirect call instructions where
         * even more arguments are used. For example, if the callee
         * expects a 'this' pointer:
         *
         *         ret = srv->network_backend_write(srv, con, con->fd, cq);
         *  40d885:   48 8b 75 e8             mov    -0x18(%rbp),%rsi
         *  40d889:   8b 56 50                mov    0x50(%rsi),%edx
         *  40d88c:   48 8b 4d e0             mov    -0x20(%rbp),%rcx
         *  40d890:   48 8b 7d f0             mov    -0x10(%rbp),%rdi
         *  40d894:   ff 97 f0 02 00 00       callq  *0x2f0(%rdi)
         *  40d89a:   89 45 dc                mov    %eax,-0x24(%rbp)
         *
         *  If the first field of a datastructure holds a function pointer, we
         *  could also see:
         *
         *         u->read_event_handler(r, u);
         *  43f0be:   ff 16                   callq  *(%rsi)
         *
         *  We only see this behavior when the indirect call instructions are
         *  optimized though.
         */
        if (!icalls_optimized()) max_arguments = getFirstReadArgRegister(block, icall_addr);

        /* Perform 'backward live analysis': starting from the last possible
         * argument register, test if these registers are written by any basic
         * block of this function that precedes the icall instruction.
         */
        
        /* First, get all the preceding basic blocks.
         * XXX The current implementation of get_preceding_bbs does not follow
         * fallthrough edges. This means that the fetching preceding blocks
         * stops at (direct) call instructions. This may actually be a good
         * thing: if we see high argument registers being written here (r8, r9),
         * we know for sure that these are not used for a direct call
         * instruction that happens to expect 5-6 arguments. On the other hand,
         * an optimization may set these registers before such call instruction
         * in which case we will underestimate.
         */
        std::set<ArmsBasicBlock *> preceding_blocks;
        std::set<ArmsBasicBlock *>::iterator iter;
        
        #ifdef BETWEEN_CALL
        std::set<ArmsBasicBlock *> preceding_blocks_old;
        block->get_preceding_bbs(&preceding_blocks_old, f->get_basic_blocks());
        unsigned long final_icall_addr  = 0;
        //std::set<ArmsBasicBlock *>::iterator it;
        for(iter = preceding_blocks_old.begin(); iter != preceding_blocks_old.end(); iter++) {
            ArmsBasicBlock *bb = *iter;
            unsigned long bb_addr = bb->get_last_insn_address();
            //it = ret_blocks.find(bb);
            if ( ret_blocks[f].find(bb) != ret_blocks[f].end() && bb_addr < icall_addr)
            {
                dprintf("indirect caller for indirect call %lx\n",bb_addr);
                if (bb_addr >= final_icall_addr)
                {
                    final_icall_addr = bb_addr;
                }
            }
            
        }
        for(iter = preceding_blocks_old.begin(); iter != preceding_blocks_old.end(); iter++) {
            ArmsBasicBlock *bb = *iter;
            if (bb->get_last_insn_address() >= final_icall_addr)
            {
                preceding_blocks.insert(bb);

            }
        }
        preceding_blocks.insert(block);
        #else
        block->get_preceding_bbs(&preceding_blocks, f->get_basic_blocks());
        preceding_blocks.insert(block);
        #endif

        
        for(iter = preceding_blocks.begin(); iter != preceding_blocks.end(); iter++) {
            ArmsBasicBlock *bb = *iter;
            dprintf("preceding block: %p - %p\n", (void *) bb->get_start_address(), (void *) bb->get_last_insn_address()); 
        } 
        
        /* if any(f->entry_blocks) in preceding_blocks:
         *      it could be that a function argument is redirect to the icall
         *      invocation directly. we must assume that the last argument may
         *      could be used with an explicit write.
         *          - we can try to rely on our function-argcount detection,
         *          however, that is an underestimation at best, so it won't be
         *          100% fool proof.  ---> found one in vsftpd :(  hash_get_bucket
         *                                      exim  - dbmdb_find
         *          - instead, we could simply maximize argcount for these icalls which is
         *          probably bad.
         *          - we will perform a recursive lookup!
         */
        



        #ifdef WRAPPER_OPT
        int CALL_PREDECESSOR = 0;
        //std::set<ArmsBasicBlock *>::iterator iter;
        for(iter = preceding_blocks.begin(); iter != preceding_blocks.end(); iter++) {
            ArmsBasicBlock *bb = *iter;
            unsigned long bb_icall_addr = bb->get_last_insn_address();
            if (ret_blocks[f].find(bb) != ret_blocks[f].end())
            {
                dprintf("indirect caller for wrapper %lx\n",bb->get_last_insn_address());
                CALL_PREDECESSOR = 1;
                break;
            }
            /*if (bb_icall_addr != icall_addr){
                for(size_t e = 0; e < bb->outgoing_edge_count(); e++) {
                    ArmsEdge *edge = bb->get_outgoing_edge(e);
                    if (edge->is_direct_call())
                    {
                        dprintf("direct caller for wrapper %lx\n",bb->get_last_insn_address());
                        CALL_PREDECESSOR = 1;
                        break;
                    }
                    
                }
            }
            if (CALL_PREDECESSOR)
                break;*/
            //dprintf("(afterset_icall_argsfollowing entries) preceding block: %p - %p\n", (void *) bb->get_start_address(), (void *) bb->get_last_insn_address()); 
        } 
        bool maybe_address_taken = false; 
        if ( !CALL_PREDECESSOR ){
            std::set<ArmsFunction *> processed_callers;
            maybe_address_taken = follow_entry_blocks(&preceding_blocks, f, &processed_callers, 0,icall_addr);
            if (maybe_address_taken) dprintf("ADDRESS COULD BE TAKEN!\n");
        }
        #else
        std::set<ArmsFunction *> processed_callers;
        bool maybe_address_taken = follow_entry_blocks(&preceding_blocks, f, &processed_callers, 0,icall_addr);
        if (maybe_address_taken) dprintf("ADDRESS COULD BE TAKEN!\n");

        #endif
        for(iter = preceding_blocks.begin(); iter != preceding_blocks.end(); iter++) {
            ArmsBasicBlock *bb = *iter;
            dprintf("(afterset_icall_argsfollowing entries) preceding block: %p - %p\n", (void *) bb->get_start_address(), (void *) bb->get_last_insn_address()); 
        } 

        /* Assume that all set_icall_argsrgument registers are written - no gaps */
                /* we need to look at the paths, and then look at the minimum.
                 * and we need to follow through direct call (get thrash registered)
                 * and we can ignore indirect calls (reuse) */
        /*int j;
        for (j = 0; j < max_arguments; j++) {
            ddprintf("  %s written in preceding blocks: %d\n", 
                            get_register_name(j).c_str(),
                            rw_registers[j].writtenInBlocks(preceding_blocks));
            if (!rw_registers[j].writtenInBlocks(preceding_blocks)) {
                break;
            }
        }
        max_arguments = j;*/

        

   

        if (maybe_address_taken) 
            /* TODO confirm that one of the addresses actually taken... */
            max_arguments = IA64_ARGS;
        dprintf("max-arguments: %d\n", max_arguments);
#endif
        /*#ifdef STRATEGY_WIDTH
        std::vector<ArmsBasicBlock *> v_preceding_blocks(preceding_blocks.size());
        std::copy(preceding_blocks.begin(),preceding_blocks.end(), v_preceding_blocks.begin());
        for ( int i =0; i < max_arguments; i++)
        {
            dprintf("Indirect callsite width     %s: %d\n",            get_register_name(i).c_str(), 
                               width_registers[i].getWidth_callsite(v_preceding_blocks));
        }
        #endif*/
        // going bold
        block->set_icall_args(max_arguments);
        #ifdef STRATEGY_WIDTH
        block->set_icall_width(arg_width);
        #endif

        #ifdef STATISTICS
        int icall_in_wrapper_v = icall_in_wrapper[icall_addr];
        int icall_bet = icall_bet_info[icall_addr];
        block->set_icall_pointer(icall_pointer);

        block->set_icall_imm(icall_imm);

        block->set_icall_13(icall13);

        block->set_icall_36(icall36);

        block->set_icall_wrapper(icall_in_wrapper_v);

        #ifdef CHECK_XOR
        block->set_icall_xor(icallxor);
        #endif
        block->set_icall_bet(icall_bet);
        /*icall_pointer = 0;

        icall_imm = 0;
        icall13 = 0;
        icall36 = 0;*/
        
        #endif

        if (min_arguments == max_arguments) {
            dprintf("!! icallsite %s.%d sets exactly %d arguments !!\n", f->get_name().c_str(), i, max_arguments);
        } else {
            dprintf(" !! icallsite %s.%d sets %d to %d arguments !!\n", f->get_name().c_str(), i, min_arguments, max_arguments);
        }
        
        std::set<ArmsFunction*> dependencies = f->get_dependencies();
            for (auto it  = dependencies.begin();
                      it != dependencies.end();
                      it++) {
                ArmsFunction *dep = *it;
                dprintf("[bt] icall %s.%d (%p) may benefit from profiling (now: %d args): lone (possible AT) function: %s (%p)\n", f->get_name().c_str(), i, (void*)block->get_last_insn_address(), max_arguments, dep->get_name().c_str(), (void *)dep->get_base_addr());
                block->add_dependency(dep);
            }
            f->clear_dependencies();
        
    }
    //debuging

    //for (auto elem: icall_with_constant)
    //{
        //dprintf("indiret call with constant arg %lx\n",elem);
    //}
}


