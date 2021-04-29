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

#ifndef __ARMS_DEREF__
#define __ARMS_DEREF__


#include <map>
    

class ArmsBasicBlock; 
class ArmsFunction;
class ArmsEdge;

typedef enum {
    D_IA64_CLEAR,     /* register was untouched */
    D_IA64_DEREF,     /* register was read and dereferenced */
    D_IA64_WRITE,     /* register was write only */
} D_StateType;

class ArmsDerefRegister {


public: 
    /* Constructor / Destructor */
	ArmsDerefRegister() {}
	~ArmsDerefRegister() {} 

    /* Iterators */
    typedef std::map <ArmsBasicBlock *, std::map <unsigned long, D_StateType> > :: iterator block_it_type;
    typedef                             std::map <unsigned long, D_StateType>   :: iterator state_it_type;
    typedef std::map <unsigned long, D_StateType>::reverse_iterator state_rit_type;

    /* Returns a string representation for a specific state */
    static string getStateName(D_StateType state);

    /* Set the register state for a specific instruction (block/offset combination) */
    void setState(ArmsBasicBlock *block, unsigned long offset, D_StateType state);
    void setDeref(ArmsBasicBlock *block, unsigned long offset);
    void setWrite(ArmsBasicBlock *block, unsigned long offset);

    bool getDeref(ArmsBasicBlock *block);

    /* Returns true if this register was deref before write within the provided blocks */
    bool isDeref(std::vector<ArmsBasicBlock *> blocks) { return getState(blocks) == D_IA64_DEREF; }

    /* Returns the RW state for this register in a specific block. This assumes
     * that the instructions for this block were parsed in consecutive order. */
    D_StateType getState(ArmsBasicBlock *block);
    /* Returns the register state for at a specific offset in a block */
    D_StateType getState(ArmsBasicBlock *block, unsigned long offset);

    /* Returns the RW state for this register in a number of blocks */
    D_StateType getState(std::vector<ArmsBasicBlock *> blocks);


    bool writtenInBlock(ArmsBasicBlock *block);

    bool writtenInBlocks(std::set<ArmsBasicBlock *> blocks);
   
    /* Returns the first basic block in which the state for this register was <state> */
    ArmsBasicBlock* getBB(std::vector<ArmsBasicBlock *> blocks, D_StateType state);
    ArmsBasicBlock* getDerefBB(std::vector<ArmsBasicBlock *> blocks) { return getBB(blocks, D_IA64_DEREF); }

    /* Returns the offset for the instruction that set the state for this register */
    unsigned long getOffset(ArmsBasicBlock *block, D_StateType state);
    unsigned long getDerefOffset(ArmsBasicBlock *block) { return getOffset(block, D_IA64_DEREF); }



private:
    std::map <ArmsBasicBlock *, std::map <unsigned long, D_StateType> > block_list;
    
};










class ArmsDeref {

#define D_IA64_RAX 0

#define D_IA64_LAST_ARG D_IA64_RAX
#define D_IA64_REGS 1 /* Number of registers that we keep track of */
#define D_IA64_ARGS 1 /* Number of registers used for arguments. Additional
                       registers (like RSP) must be placed after the register
                       arguments. */


public:
    ArmsDeref() {}

    ~ArmsDeref() {}

    /* returns a string representation of for a specific regiser index */
    static string get_register_name(int reg);
    /* callback for foreach_function(). arg should be a pointer to an
     * ArmsDeref instance */
    static int parse_functions(ArmsFunction *f, void *arg);

    void set_bpatch_image(BPatch_image *image) { image = image; };
   
    /* Get the argument count for a given arms function */
    int get_callee_retuse(ArmsFunction *f); 
    int get_caller_retuse(ArmsFunction *f);
    int get_vararg_count(ArmsFunction *f); 

    int get_icallsites(ArmsFunction *f);

private:
    ArmsDerefRegister rw_registers[D_IA64_REGS];

    /* blocks that have been analyzed */
    std::set<ArmsBasicBlock *>  analyzed_blocks; 

    /* blocks per function, stored in a vector so we control the ordering */
    std::map<ArmsFunction *, std::vector<ArmsBasicBlock *> > function_blocks;

    /* blocks per function that end with an indirect call instruction */
    std::map<ArmsFunction *, std::set<ArmsBasicBlock *> > icall_blocks;
    
    //added by yanlin
    std::map<ArmsFunction *, std::set<ArmsBasicBlock *> > call_blocks;

    BPatch_image *image;


    bool is_analyzed(ArmsBasicBlock *bb);
    std::string bm_tostring(int reg_bitmap);
    
    void parse_register(RegisterAST::Ptr reg, 
                        ArmsBasicBlock *bb, unsigned long offset, D_StateType state);
    void parse_register_set(std::set<RegisterAST::Ptr> register_set, 
                            ArmsBasicBlock *bb, unsigned long offset, D_StateType state);
    void parse_instruction(Instruction::Ptr iptr,
                           ArmsBasicBlock *bb, unsigned long offset);
    void parse_block(ArmsFunction *f, ArmsBasicBlock *bb);
    int parse_function(ArmsFunction *f);

    bool getForwardLiveness(ArmsFunction *f,
                                     ArmsBasicBlock *bb);
    uint16_t getForwardLiveness2(ArmsFunction *f,
                                     ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> fts,
            std::vector<ArmsBasicBlock *> argcount_analyzed_blocks);

    uint16_t getBackwardLiveness(ArmsFunction *f,
                                       ArmsBasicBlock *bb,
            std::vector<ArmsBasicBlock *> callsite_analyzed_blocks);

    RegisterAST::Ptr is_dereference(Instruction::Ptr iptr);
    bool computation_used(Instruction::Ptr iptr);
    bool icalls_optimized(void);

    /* worst-case scenario, assume optimized */
    bool is_optimized = true;
    bool opt_detector_completed = false;
    
    string get_regstate_name(int i, ArmsFunction *f);

    /* instruction length per offset */
    std::map <unsigned long, unsigned long> ins_length;
    
    /* for our recursion strategy */
    D_StateType argc_registers[D_IA64_ARGS];
    std::set<ArmsBasicBlock *> argc_analyzed_blocks;

    std::map <ArmsBasicBlock *, uint16_t> backward_cache;
    std::map <ArmsBasicBlock *, uint16_t> forward_cache;

};
#endif 
