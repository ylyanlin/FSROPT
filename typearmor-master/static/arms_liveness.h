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

#ifndef __ARMS_LIVENESS__
#define __ARMS_LIVENESS__

//added by yanlin
#define PARSE_DATA_SECTION 
#define STRATEGY_WIDTH
#define SixToThree
#define STATISTICS
#define CHECK_XOR
//end

#include <map>
    

class ArmsBasicBlock; 
class ArmsFunction;
class ArmsEdge;

typedef enum {
    IA64_CLEAR,     /* register was untouched */
    IA64_READ,      /* register was read only */
    IA64_WRITE,     /* register was write only */
    IA64_RW,        /* register was read and write */
} StateType;

class ArmsRegister {


public: 
    /* Constructor / Destructor */
	ArmsRegister() {}
	~ArmsRegister() {} 

    /* Iterators */
    typedef std::map <ArmsBasicBlock *, std::map <unsigned long, StateType> > :: iterator block_it_type;
    typedef                             std::map <unsigned long, StateType>   :: iterator state_it_type;
    typedef                             std::map <unsigned long, bool>        :: iterator deref_it_type;
    /* added by yanlin */
    typedef                             std::map <unsigned long, int>         :: iterator register_it_width;
    typedef std::map <unsigned long, StateType>::reverse_iterator state_rit_type;

    /* Returns a string representation for a specific state */
    static string getStateName(StateType state);

    /* Set the register state for a specific instruction (block/offset combination) */
    void setState(ArmsBasicBlock *block, unsigned long offset, StateType state);
    void setRead (ArmsBasicBlock *block, unsigned long offset);
    void setWrite(ArmsBasicBlock *block, unsigned long offset);

    /* added by yanlin. */
    void setWidth_read(ArmsBasicBlock *block, unsigned long offset, int width);
    void setWidth_write(ArmsBasicBlock *block, unsigned long offset, int width);
    int getwidth_write(ArmsBasicBlock *block, unsigned long offset);
    int getWidth_callee(ArmsBasicBlock *block);
    bool isWrite(ArmsBasicBlock *block);
    int getWidth_callsite(ArmsBasicBlock *block);
    int getWidth_offset(ArmsBasicBlock *block, unsigned long offset);
    bool writtenInCaller(ArmsBasicBlock *block);
    void setStateCaller(ArmsBasicBlock *block, unsigned long offset, StateType state);
    bool readInCaller(ArmsBasicBlock *block);
    std::map <unsigned long, StateType> getStateCaller(ArmsBasicBlock *block);
    //test 
    void insn_test(ArmsBasicBlock *block, unsigned long offset, std::string ins_str);
    int data_instruction_test(ArmsBasicBlock *block);

    /* by yanlin*/
    void offsetToins(ArmsBasicBlock *block, unsigned long offset, Instruction::Ptr iptr);
    RegisterAST::Ptr readARGtoARG(ArmsBasicBlock *bb,Instruction::Ptr iptr,unsigned int offset);
    /*end */
    #ifdef SixToThree
    int getSixtoThree(ArmsBasicBlock *block);
    int write32bit(Instruction::Ptr iptr);
    #endif

    
    
    //end of yanlin

    void setDeref(ArmsBasicBlock *block, unsigned long offset);
    bool getDeref(ArmsBasicBlock *block);


    /* Returns true if this register was read before write within the provided blocks */
    bool isRead(std::vector<ArmsBasicBlock *> blocks) { return getState(blocks) == IA64_READ; }

    /* Returns the RW state for this register in a specific block. This assumes
     * that the instructions for this block were parsed in consecutive order. */
    StateType getState(ArmsBasicBlock *block);
    /* Returns the register state for at a specific offset in a block */
    StateType getState(ArmsBasicBlock *block, unsigned long offset);

    /* Returns the RW state for this register in a number of blocks */
    StateType getState(std::vector<ArmsBasicBlock *> blocks);

    /* added by yanlin. return the width for this register in a number of blocks */
    int getWidth_callee(std::vector<ArmsBasicBlock *> blocks);
    int getWidth_callsite(std::vector<ArmsBasicBlock *> blocks);

    StateType getLastState(ArmsBasicBlock *block);

    bool writtenInBlock(ArmsBasicBlock *block);
    
    bool writtenLastInBlock(ArmsBasicBlock *block);

    bool writtenInBlocks(std::set<ArmsBasicBlock *> blocks);
   
    /* Returns the first basic block in which the state for this register was <state> */
    ArmsBasicBlock* getBB(std::vector<ArmsBasicBlock *> blocks, StateType state);
    ArmsBasicBlock* getReadBB(std::vector<ArmsBasicBlock *> blocks) { return getBB(blocks, IA64_READ); }

    /* Returns the offset for the instruction that set the state for this register */
    unsigned long getOffset(ArmsBasicBlock *block, StateType state);
    unsigned long getReadOffset(ArmsBasicBlock *block) { return getOffset(block, IA64_READ); }



private:
    std::map <ArmsBasicBlock *, std::map <unsigned long, StateType> > block_list;
    std::map <ArmsBasicBlock *, std::map <unsigned long, bool> > deref_block_list;
    
    /* added by yanlin */ 
    std::map <ArmsBasicBlock *, std::map <unsigned long, int> > block_list_width_write;
    std::map <ArmsBasicBlock *, std::map <unsigned long, int> > block_list_width_read;
    std::map <ArmsBasicBlock *, std::map <unsigned long, StateType> > block_list_caller;
    std::map <ArmsBasicBlock *, std::map <unsigned long, std::string> > ins_list;
    std::map <ArmsBasicBlock *, std::map <unsigned long, Instruction::Ptr> > offset2ins;
    std::map <ArmsBasicBlock *, std::map <unsigned long, int> > reg_width_list;
    
};










class ArmsLiveness {

#define IA64_RDI 0
#define IA64_RSI 1
#define IA64_RDX 2
#define IA64_RCX 3
#define IA64_R8  4
#define IA64_R9  5
#define IA64_RSP 6 /* to identify varargs */
#define IA64_RBP 7
#define IA64_RAX 8
#define IA64_R10 9
#define IA64_RBX 10
//added by yanlin
#define IA64_R11 11
#define IA64_R12 12
#define IA64_R13 13
#define IA64_R14 14
#define IA64_R15 15


#define IA64_LAST_ARG IA64_R9
#define IA64_REGS 16 /* Number of registers that we keep track of */
#define IA64_ARGS 6 /* Number of registers used for arguments. Additional
                       registers (like RSP) must be placed after the register
                       arguments. */


public:
    ArmsLiveness() {}

    ~ArmsLiveness() {}

    /* returns a string representation of for a specific regiser index */
    static string get_register_name(int reg);
    /* callback for foreach_function(). arg should be a pointer to an
     * ArmsLiveness instance */
    //revised by yanlin
    static int parse_functions(ArmsFunction *f, void *arg, std::vector<std::vector<unsigned long>> data_info);
    //original
    //static int parse_functions(ArmsFunction *f, void *arg);

    //added by yanlin
    static int parse_functions_second_time(ArmsFunction *f, void *arg);
    //end of yanlin

    void set_bpatch_image(BPatch_image *image) { image = image; };
   
    /* Get the argument count for a given arms function */
    int get_arg_count(ArmsFunction *f); 
    int get_vararg_count(ArmsFunction *f); 

    //added by yanlin
    //int entryToDirectCall(ArmsFunction *f);
    int DirectCallREGReads(ArmsFunction *f);
    //end of yanlin

    int get_icallsites(ArmsFunction *f);

private:
    ArmsRegister rw_registers[IA64_REGS];
    //added by yanlin
    ArmsRegister width_registers[IA64_REGS];

    ArmsRegister caller_registers[IA64_REGS];

    /* blocks that have been analyzed */
    std::set<ArmsBasicBlock *>  analyzed_blocks; 

    /* blocks per function, stored in a vector so we control the ordering */
    std::map<ArmsFunction *, std::vector<ArmsBasicBlock *> > function_blocks;

    #ifdef STRATEGY_WIDTH
    std::map<address_t, std::vector<int> > function_argwidth;
    std::map<ArmsBasicBlock *, std::vector<int> > block_argwidth;
    #endif

    //added by yanlin
    std::map<address_t, ArmsFunction *> all_functions;
    //end of yanlin

    /* blocks per function that end with an indirect call instruction */
    std::map<ArmsFunction *, std::set<ArmsBasicBlock *> > icall_blocks;

    //added by yanlin
    /* blocks per function that end with a direct call instruction */
    std::map<ArmsFunction *, std::set<ArmsBasicBlock *> > call_blocks;
    /* blocks  that end with a ret instruction */
    std::map<ArmsFunction *, std::set<ArmsBasicBlock *> > ret_blocks;
    //end of yanlin

    BPatch_image *image;

    /* return the first argument register that is read at a specific offset within a
     * given basic block. */
    int getFirstReadArgRegister(ArmsBasicBlock *bb, unsigned long offset);

    bool is_analyzed(ArmsBasicBlock *bb);

    
    
    std::string bm_tostring(int reg_bitmap);

    #ifdef PARSE_DATA_SECTION
    void parse_register(Instruction::Ptr iptr, std::vector<std::vector<unsigned long>> data_info,
                        RegisterAST::Ptr reg, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state);
    #else
    void parse_register(RegisterAST::Ptr reg, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state);
    #endif
    //revised by yanlin
    #ifndef PARSE_DATA_SECTION
    void parse_register_set(std::set<RegisterAST::Ptr> register_set, 
                            ArmsBasicBlock *bb, unsigned long offset, StateType state);
    #else
    void parse_register_set(Instruction::Ptr iptr, std::vector<std::vector<unsigned long>> data_info, std::set<RegisterAST::Ptr> register_set, 
                            ArmsBasicBlock *bb, unsigned long offset, StateType state);
    #endif

    #ifdef PARSE_DATA_SECTION
    void parse_instruction(Instruction::Ptr iptr,
                           ArmsBasicBlock *bb, unsigned long offset,std::vector<std::vector<unsigned long>> data_info);
    #else
    void parse_instruction(Instruction::Ptr iptr,
                           ArmsBasicBlock *bb, unsigned long offset);
    #endif
    //revised by yanlin
    #ifdef PARSE_DATA_SECTION
    void parse_block(ArmsFunction *f, ArmsBasicBlock *bb,std::vector<std::vector<unsigned long>> data_info);
    #else
    void parse_block(ArmsFunction *f, ArmsBasicBlock *bb);
    #endif

    //revised by yanlin
    int parse_function(ArmsFunction *f,std::vector<std::vector<unsigned long>> data_info);
    // original
    //parse_function(ArmsFunction *f);
  

    bool getForwardLiveness(ArmsFunction *f,
                                     ArmsBasicBlock *bb);
    std::vector<uint32_t> getForwardLiveness2(ArmsFunction *f,
                                     ArmsBasicBlock *bb,
                                     ArmsBasicBlock *prevBB,
            std::vector<ArmsBasicBlock *> fts,
            std::vector<ArmsBasicBlock *> argcount_analyzed_blocks,
            std::vector<uint16_t> *reg_width,
            std::vector<int> first_flag);
   
    bool getRAXreads(ArmsFunction *f,
            ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> retuse_fts,
            std::vector<ArmsBasicBlock *> retuse_analyzed_blocks);
    bool getRAXwrites(ArmsFunction *f,
                      ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> callee_retuse_analyzed_blocks);

    std::vector<uint32_t> getBackwardLiveness(ArmsFunction *f,
                                       ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> &callsite_analyzed_blocks, int depth,
            unsigned long icall_addr,std::vector<int>first_write);

    RegisterAST::Ptr is_dereference(Instruction::Ptr iptr);
    bool computation_used(Instruction::Ptr iptr);
    bool icalls_optimized(void);

    /* worst-case scenario, assume optimized */
    bool is_optimized = true;
    bool opt_detector_completed = false;
    
    bool also_read(int first_vararg, ArmsBasicBlock *first_bb, int reg_index);
    //added by yanlin
    int VarConsecutive(ArmsBasicBlock *bb, int m,int begin,int last_stack_offset, ParseAPI::Block::Insns insns);
    int consecutiveAddress(ArmsBasicBlock *bb, int m, int n, int last_stack_offset);
    bool read_stack(ArmsBasicBlock *bb, int reg_index, unsigned long offet);
    int get_offset(std::string ins_str);
    bool allConsecutive(ArmsBasicBlock *bb, int m,int begin,int last_stack_offset, ParseAPI::Block::Insns insns);
    bool reuseOperand(ArmsFunction *f, std::string op, ArmsBasicBlock *last_bb);
    //bool directCall_follow_entry_blocks(std::set<ArmsBasicBlock *> *preceding_blocks, ArmsFunction *f, 
                                                  //unsigned long dcall_addr);
    
    ArmsFunction * find_function(address_t base_address);
    int traceCaller(ArmsBasicBlock *bb);
    void parse_caller(ArmsBasicBlock *bb);
    void parse_caller_instruction(Instruction::Ptr iptr,
                                     ArmsBasicBlock *bb, unsigned long offset);
    void parse_register_set_caller(std::set<RegisterAST::Ptr> register_set, 
                        ArmsBasicBlock *bb, unsigned long offset, StateType state);
    void parse_register_caller(RegisterAST::Ptr reg, 
                                  ArmsBasicBlock *bb, unsigned long offset, StateType state);
    
    #ifdef PARSE_DATA_SECTION
    int icall_statis(std::vector<ArmsBasicBlock *> blocks, address_t icall_addr, std::vector<uint16_t> reg_width, int argcount);
    //0:non-constant, 1: data pointer, 2:immediate value
    int isConstantArg(Instruction::Ptr iptr,std::vector<std::vector<unsigned long>> data_info);
    
    int isbbConstantArg(ArmsBasicBlock *bb, int i);
    int isbbConstantArgFirst(ArmsBasicBlock *block, int t);
    #endif

    #ifdef SixToThree
    int isRead64To32(Instruction::Ptr iptr,ArmsBasicBlock *bb, unsigned long offset,int t);
    int ispush(Instruction::Ptr iptr,ArmsBasicBlock *bb, unsigned long offset,int t);
    int isRead32To64(Instruction::Ptr iptr,ArmsBasicBlock *bb, unsigned long offset, int i);
    int isRead16To32(Instruction::Ptr iptr,ArmsBasicBlock *bb, unsigned long offset, int i);
    int isBBRead64To32(ArmsBasicBlock *bb, int i);
    int isBBpush(ArmsBasicBlock *bb, int i);
    int isBBRead32To64(ArmsBasicBlock *bb, int i);
    int isBBRead16To32(ArmsBasicBlock *bb, int i);
    #endif

    #ifdef CHECK_XOR
    int isXorIns(Instruction::Ptr iptr, ArmsBasicBlock *bb, unsigned long offset, int i);
    int isBBXorIns(ArmsBasicBlock *bb, int i);
    int isBBXorFirst(ArmsBasicBlock *block, int t);
    #endif

    bool getREGreads(ArmsFunction *f, ArmsBasicBlock *bb, int depth, int reg,
                    std::vector<ArmsBasicBlock *> retuse_fts,
                    std::vector<ArmsBasicBlock *> retuse_analyzed_blocks);
    
    bool REGreads(ArmsFunction *f, ArmsBasicBlock *bb,
                    std::vector<ArmsBasicBlock *> retuse_fts,
                    std::vector<ArmsBasicBlock *> retuse_analyzed_blocks);
    
    
    //end of yanlin

    int is_variadic(ArmsFunction *f);
    string get_regstate_name(int i, ArmsFunction *f);

    /* instruction length per offset */
    std::map <unsigned long, unsigned long> ins_length;
    
    /* for our recursion strategy */
    StateType argc_registers[IA64_ARGS];
    std::set<ArmsBasicBlock *> argc_analyzed_blocks;

    std::map <ArmsBasicBlock *, uint16_t> backward_cache;
    std::map <ArmsBasicBlock *, uint16_t> forward_cache;

    #ifdef STRATEGY_WIDTH
	std::vector<uint16_t> arg_width;
	struct result
    {
        uint16_t reg_bitmap;
        std::vector<int> reg_width_vector;
    };

    std::map <ArmsBasicBlock *, std::vector<uint32_t> > forward_result;

	#endif

    //added by yanlin
    std::set<ArmsBasicBlock *> analyzed_bb;
    #ifdef PARSE_DATA_SECTION
    std::vector<std::vector<unsigned long>> dataInfo;
    std::map <ArmsBasicBlock *, std::map <unsigned long, int> > insn_constant;
    //std::map<unsigned long, uint16_t > insn_constant;
    std::set<address_t> icall_with_constant;
    #endif

    #ifdef SixToThree
    std::map <ArmsBasicBlock *, std::map <unsigned long, int> > read64to32;
    
    // Functions that reads 64 bit but writes to 32bit
    std::map <address_t,  std::map <int, int>>  Fread64to32;
    
    std::map <ArmsBasicBlock *, std::map <unsigned long, int> > read32to64;
    std::map <address_t, std::map <int, int> > FunctionR63;
    std::map <ArmsBasicBlock *, std::map <int, int> > BBR36;
    std::map <ArmsBasicBlock *, std::map <int, int> > BBR13;
    std::map <ArmsBasicBlock *, std::map <int, int> > BBConstant;
    std::map <ArmsBasicBlock *, std::map <int, int> > BBicallXor;
    #endif 

    #ifdef STATISTICS
    //std::set<address_t> icall_in_wrapper_taken;
    //std::set<address_t> icall_in_wrapper_Dcall;

    std::map<address_t,int > icall_in_wrapper;
    std::map<address_t, int> icall_bet_info;
    //std::map<address_t,int > icall_in_wrapper_Dcall;

    std::map<address_t,std::map <int, int> > icall_constant;

    std::map<address_t,std::map <int, int> > icall_R13;

    std::map<address_t,std::map <int, int> > icall_R36;

    std::map<address_t,std::map <int, int> > icall_xor;

    //std::set<address_t> ReadRDX;
    /*std::set<int>  icall_pointer;
    std::set<int>  icall_imm ;
    //std::set<address_t> icall_imm;
    std::set<int>  icall36;
    std::set<int>  icall13;*/
    #endif

};
#endif 
