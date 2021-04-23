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

#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <limits.h>
#include <assert.h>
#include <iostream>
#include <string>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <algorithm>  

#include <fstream>
#include <tuple>
#include <list>
#include <vector>

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <string.h>

#include "BPatch.h"
#include "BPatch_addressSpace.h"
#include "BPatch_process.h"
#include "BPatch_object.h"
#include "BPatch_binaryEdit.h"
#include "BPatch_function.h"
#include "BPatch_point.h"
#include "BPatch_flowGraph.h"
#include "BPatch_memoryAccessAdapter.h"

#include "PatchCommon.h"
#include "PatchMgr.h"
#include "PatchModifier.h"

#include "Register.h"

using namespace std;
using namespace Dyninst;
using namespace Dyninst::PatchAPI;
using namespace Dyninst::ParseAPI;
using namespace Dyninst::InstructionAPI;
using namespace Dyninst::SymtabAPI;

#include "function.h"
#include "instPoint.h"

#include "env.h"
#include "defs.h"
#include "arms_utils.h"
#include "arms_bb.h"
#include "arms_edge.h"
#include "arms_function.h"
#include "arms_cfg.h"
#include "arms_dyninst_cfg.h"
#include "arms_liveness.h"

#include <dynProcess.h>
#include <AddrLookup.h>
#include <liveness.h>

#include <pass.h>

PASS_ONCE();

/* meh */
#define SYMBOLS_AVAILABLE 1

#define __PASS_DEBUG 1

#define fcfiPassLog(M) (cout << "FCFIPass: " << M << "\n")
#define fcfiPassDbg(M) DEBUG(dbgs() << "FCFIPass [DEBUG]: " << M << "\n")

//added by yanlin
//#define FOLLOW_DIRECT_CALL
//#define CHECK_DCALL
#define STATISTICS
#define STRATEGY_WIDTH 
//end of yanlin

static cl::opt<std::string>
optAT("at",
    cl::desc("AT output"),
    cl::init("at.txt"));

static cl::opt<std::string>
optBinfo("binfo",
    cl::desc("output binfo prefix"),
    cl::init("binfo"));

static cl::opt<bool>
optUnused("unused",
    cl::desc("Search for unused functions"),
    cl::init(false));


#include <PatchModifier.h>


using namespace Dyninst::PatchAPI;
using namespace Dyninst::InstructionAPI;
using namespace Dyninst::SymtabAPI;

#include <errno.h>

/* I will stick to the easy case: if a function has
 * - ZERO incoming edges
 * - is NOT address taken
 * I will mark it as 'unused'
 *
 * I do not follow through direct calls for now. So if function X is called only
 * by Y while Y is never called, I will not mark it as unused.
 */


class Unused {

public:
	Unused(ArmsFunction *f) {
        libname = f->get_cfg()->get_module_name();
        fname =          f->get_name();
        faddr = (void *) f->get_base_addr();
        intermodulair = false;

        std::map<ArmsBasicBlock *, int> icall_args = f->get_icall_args();
        for (auto it : icall_args) {
            ArmsBasicBlock *block = it.first;
            callsites.push_back( (void *) block->get_last_insn_address() );
        }
    }

    string libname;
    string fname;
    void * faddr;
    bool intermodulair;
    std::vector<void *> callsites;
};


/* lazy enough to make this global */
std::vector<Unused> *unused_p;

typedef tuple<address_t, address_t, int, bool,address_t, address_t> mytuple;
vector<mytuple> icall_info;
vector<mytuple> func_info;
//vector<mytuple> iret;
std::map<address_t,ArmsFunction *> all_funcs;
std::map<address_t,ArmsBasicBlock *> tail_blocks;

//typedef map<address_t,std::vector<address_t>> CFG;
//std::map<int,CFG > all_CFG;

//std::tuple<int,address_t,std::vector<address_t>> all_CFG;

//std::map<address_t,std::vector<address_t>> CFI;

std::map<std::tuple<int, address_t,address_t>,std::vector<std::pair<address_t,address_t>>> all_CFG;


//std::vector<std::tuple<address_t, int, bool>> *icall_info;
//std::vector<std::tuple<address_t, int, bool>> *func_info;


static int process_vararg_function(ArmsFunction *f, void *arg) {
    ArmsLiveness *alive = (ArmsLiveness *) arg;
    alive->get_vararg_count(f);

    return 0;
}


/* Essentially what we want to do here is intermodulair dead code ellimination
 * on a function level. Or 'recursive inlining'. We don't go that far, we just
 * elliminate the easy stuff.
 */
static int process_unused_function(ArmsFunction *f, void *arg) {
    // only if this is a PLT stub
    if (!f->is_plt()) return 0;

    for (int i = 0; i < unused_p->size(); i++) {
        if (f->get_name() == (*unused_p)[i].fname) {

            /* This means that there exists a PLT stub that calls a function
             * that has the same name of a function which we previously though
             * was not used (i.e., it is not AT and it did not have any incoming
             * edges). */
            (*unused_p)[i].intermodulair = true;
            /* Without doing special tricks, we can only map on the function
             * name. We must thus continue our search: maybe there is another
             * previously thought unused function that has the same function
             * name. */

            assert(f->get_entry_points()->size() == 1);
        }
    }

    return 0;
}

static int process_function(ArmsFunction *f, void *arg) {
    ArmsLiveness *alive = (ArmsLiveness *) arg;
    alive->get_arg_count(f);

    return 0;
}

//added by yanlin
/*#ifdef FOLLOW_DIRECT_CALL
static int parse_functions_second_time(ArmsFunction *f, void *arg)
{
    ArmsLiveness *alive = (ArmsLiveness *) arg;
    //dprintf("parse function again\n");
    alive->entryToDirectCall(f);
    return 0;
}
#endif*/

static int process_function_callsites(ArmsFunction *f, void *arg) {
    /* Cannot be combined with above as this expects all argcounts to be
     * available */
    ArmsLiveness *alive = (ArmsLiveness *) arg;
    alive->get_icallsites(f);

    //added by yanlin
    #ifdef CHECK_DCALL
    alive->DirectCallREGReads(f);
    #endif 

    return 0;
}

FILE* fp;

ArmsFunction * find_function(address_t base_address){

	std::map<address_t, ArmsFunction *>::iterator it = all_funcs.find(base_address);
	if (it == all_funcs.end())
		return NULL;

	return it->second;
}

address_t is_tail_block(ArmsBasicBlock *bb){

        for (size_t i = 0; i<bb->outgoing_edge_count();i++){
            ArmsEdge *e = bb->get_outgoing_edge(i);
            ArmsBasicBlock * target_bb = e->target();
            address_t base_address = target_bb->get_start_address();
            ArmsFunction *f = find_function(base_address);
            std::set<ArmsBasicBlock *> *blocks = f->get_basic_blocks();
            for (std::set<ArmsBasicBlock *>::iterator it  = blocks->begin();it != blocks->end();it++)
            {
                ArmsBasicBlock *block = *it;
                std::map<address_t,ArmsBasicBlock *> :: iterator it_tail = tail_blocks.find(block->get_start_address());
                if (it_tail != tail_blocks.end()){
                   // tail_functions[bb->get_last_insn_address()] = f;
                    if (!is_tail_block(block)){
                        ArmsEdge *ee = block->get_outgoing_edge(0);
                        ArmsBasicBlock *target2_bb = ee->target();
                        ArmsFunction *f_ret = find_function(target2_bb->get_start_address());
                        std:set<ArmsBasicBlock *> *blocks_ret =f_ret->get_basic_blocks();
                        for (std::set<ArmsBasicBlock *>::iterator it_ret  = blocks_ret->begin();it_ret != blocks_ret->end();it_ret++)
                        {
                            ArmsBasicBlock *block_ret = *it_ret;
                            if (block_ret->is_exit_block())
                            {
                                //cout << "ret for tail call: "<< block_ret->get_last_insn_address() << " "<<bb->get_last_insn_address()<<endl;
                                return block_ret->get_last_insn_address();
                            }
                        }


                    }
                  //  return true;

                }

            }
        }
        return NULL;

    }





static int print_variadics(ArmsFunction *f, void *arg) {
    std::set<void *> *at_funcs = (std::set<void *> *) arg;

    if(f->is_plt() || f->is_lib_dummy()) return 0;
    if (!f->is_variadic()) return 0;

    fprintf(fp,"%p = %d (%s) ", (void *)f->get_base_addr(), f->get_argcount(), f->getMangledName().c_str());
    if (at_funcs->count((void *)f->get_base_addr())) {
        fprintf(fp," AT");
    }
    #ifdef STRATEGY_WIDTH
    std::vector<uint16_t> arg_width = f->get_argwidth();
    for (auto elem : arg_width)
    {
        fprintf(fp,"%d ",elem);
    }
    #endif 

    #ifdef STATISTICS
    if (f->is_variadic_over())
    {
        fprintf(fp,"variadic_over");
    }
    #endif



    fprintf(fp,"\n");

    // added to get information about indirect call and indirect return branches
    address_t iret_begin;
    address_t iret_src;
    bool has_ret = false;
    std::set<ArmsBasicBlock*> *blocks = f->get_basic_blocks();
    if (f->is_plt())
    {
        iret_src = 0;
    }
    ArmsBasicBlock *entry = *(blocks->begin());
    address_t end_addr = entry->get_last_insn_address();
    for (std::set<ArmsBasicBlock *>::iterator it  = blocks->begin();it != blocks->end();it++)
    {
        ArmsBasicBlock *block = *it;
        if (block->is_exit_block())
        {
            has_ret = true;
            iret_begin = block->get_start_address();
            iret_src = block->get_last_insn_address();
        }

    }
    // for indirect call instruction calls a function which never returns or jumps to another function
    if (!has_ret){
        for (std::set<ArmsBasicBlock *>::iterator it2  = blocks->begin();it2 != blocks->end();it2++)
        {
            ArmsBasicBlock * block2 = *it2;
           // if (is_tail_block(block2))
           //iret_src = is_tail_block(block2);


        }

    }


    if (f->get_write_rax()){
        auto t = std::make_tuple(f->get_base_addr(), end_addr, f->get_argcount(),true,iret_begin,iret_src);
        func_info.push_back(t);

    }
    else
    {
        auto t = std::make_tuple(f->get_base_addr(), end_addr, f->get_argcount(),false,iret_begin,iret_src);
        func_info.push_back(t);

    }

    return 0;
}

static int print_regulars(ArmsFunction *f, void *arg) {
    std::set<void *> *at_funcs = (std::set<void *> *) arg;

    if(f->is_plt() || f->is_lib_dummy()) return 0;
    if (f->is_variadic()) return 0;

    fprintf(fp,"%p = %d (%s) ", (void *)f->get_base_addr(), f->get_argcount(), f->getMangledName().c_str());
    
     
    if (at_funcs->count((void *)f->get_base_addr())) {
        fprintf(fp," AT");
    }
    #ifdef STRATEGY_WIDTH
    std::vector<uint16_t> arg_width = f->get_argwidth();
    for (auto elem : arg_width)
    {
        fprintf(fp,"%d ",elem);
    }
    #endif

    int reg_bitmap = f->get_argbitmap();
    fprintf(fp,"reg_bitmap:");
    for (int reg_index = 0; reg_index < 6; reg_index++)
    {
        int value = reg_bitmap >> (reg_index * 2) & 0x03;
        fprintf(fp,"%d",value);
    }
    fprintf(fp," ");

    #ifdef STATISTICS
    int ReadRDX = f->get_readRDX();
    if (ReadRDX)
    {
        fprintf(fp, "readRDX ");
    }

    std::vector<int> Fread64to32 = f->get_Fread64to32();
    int mycount = std::count(Fread64to32.begin(),Fread64to32.end(),0);
    if (mycount < Fread64to32.size())
    {
        fprintf(fp,"read63{");
        for (auto elem:Fread64to32)
        {
            if (elem)
                fprintf(fp,"%d,",elem);
        }
        fprintf(fp,"} ");
    }
    
    /*if (Fread64to32)
    {
        fprintf(fp, "read63(%d) ",Fread64to32);
    }*/
    #endif 


    fprintf(fp,"\n");
    fprintf(stderr,"finished callee setting at pass\n");

   // added by yanlin

    address_t iret_begin;
    address_t iret_src;
    bool has_ret = false;
    std::set<ArmsBasicBlock*> *blocks = f->get_basic_blocks();
    if (f->is_plt())
    {
        iret_src = 0;
    }
    ArmsBasicBlock *entry = *(blocks->begin());
    address_t end_addr = entry->get_last_insn_address();
    for (std::set<ArmsBasicBlock *>::iterator it  = blocks->begin();it != blocks->end();it++)
    {
        ArmsBasicBlock *block = *it;
        if (block->is_exit_block())
        {
            has_ret = true;
            iret_begin = block->get_start_address();
            iret_src = block->get_last_insn_address();
        }

    }
    // for indirect call instruction calls a function which never returns or jumps to another function
    if (!has_ret){

        //iret_src = 1;
        for (std::set<ArmsBasicBlock *>::iterator it2  = blocks->begin();it2 != blocks->end();it2++)
        {
            ArmsBasicBlock * block2 = *it2;
           // if (is_tail_block(block2))
          // iret_src = is_tail_block(block2);
          iret_src = 0;
        }

    }

    if (f->get_write_rax()){
        auto t = std::make_tuple(f->get_base_addr(), end_addr, f->get_argcount(),true, iret_begin, iret_src);
        func_info.push_back(t);

    }
    else
    {
        auto t = std::make_tuple(f->get_base_addr(), end_addr, f->get_argcount(),false,iret_begin,iret_src);
        func_info.push_back(t);

    }

    return 0;
}

static int print_disas_errs(ArmsFunction *f, void *arg) {
    std::set<ArmsBasicBlock*> *blocks = f->get_basic_blocks();

    for (std::set<ArmsBasicBlock *>::iterator it  = blocks->begin();
                                              it != blocks->end();
                                              it++) {
        ArmsBasicBlock *block = *it;
        if (block->is_disas_err()) {

            fprintf(fp,"%p = %s\n", (void *) block->is_disas_err(), f->getMangledName().c_str());

            return 0;
        }
    }
    return 0;
}


static int print_icalls(ArmsFunction *f, void *arg) {
    std::set<void *> *at_funcs = (std::set<void *> *) arg;


    std::vector<ArmsBasicBlock*> entry_blocks;
    entry_blocks.assign(f->get_entry_points()->begin(), f->get_entry_points()->end());

    bool is_unused = true;
    while(entry_blocks.size() > 0) {
        ArmsBasicBlock *bb = entry_blocks.back();
        entry_blocks.pop_back();

        if (bb->incoming_edge_count() != 0) {
            is_unused = false;
            break;
        }
        if (at_funcs->count((void *)f->get_base_addr())) {
            is_unused = false;
            break;
        }
    }

    if (is_unused)
        unused_p->push_back( Unused(f) );


    std::map<ArmsBasicBlock *, int> icall_args = f->get_icall_args();
    int i = 0;

    std::set<ArmsBasicBlock*> *blocks = f->get_basic_blocks();

    #ifdef STRATEGY_WIDTH
    std::map<ArmsBasicBlock *, std::vector<uint16_t>> arg_width = f->get_icall_width();
    #endif

    #ifdef STATISTICS
    std::map<ArmsBasicBlock *, std::vector<int>> icallpointer = f->get_icall_pointer();
    std::map<ArmsBasicBlock *, std::vector<int>> icallimm = f->get_icall_imm();
    std::map<ArmsBasicBlock *, std::vector<int>> icall13 = f->get_icall_13();
    std::map<ArmsBasicBlock *, std::vector<int>> icall36 = f->get_icall_36();
    std::map<ArmsBasicBlock *, int> icallwrapper = f->get_icall_wrapper();
    std::map<ArmsBasicBlock *, std::vector<int>> icallxor = f->get_icall_xor();
    //printf("get icall_bet\n");
    std::map<ArmsBasicBlock *, int> icallbet = f->is_icall_bet();
    //printf("get icall_bet finished\n");
    
    #endif 

    for (auto it : icall_args){
        ArmsBasicBlock *block = it.first;
        int args = it.second;
        
        for (std::set<ArmsBasicBlock *>::iterator ii  = blocks->begin();ii != blocks->end();ii++)
        {
            ArmsBasicBlock *call = *ii;
            if (block->get_start_address() ==  call->get_start_address())
            {
                ArmsBasicBlock *next = *(++ii);
                address_t ret_begin = next->get_start_address();
                address_t ret_end = next->get_last_insn_address();
                if (block->get_read_rax()){
                    auto t = std::make_tuple(block->get_start_address(),block->get_last_insn_address(), args,true,ret_begin,ret_end);
                    icall_info.push_back(t);

                }
                else
                {
                    auto t = std::make_tuple(block->get_start_address(),block->get_last_insn_address(), args,false,ret_begin,ret_end);
                    icall_info.push_back(t);

                }
                continue;

            }

        }
    }

    /*for (std::set<ArmsBasicBlock *>::iterator ii  = blocks->begin();ii != blocks->end();ii++)
    {
         for (auto it : icall_args){
            ArmsBasicBlock *block = it.first;
            int args = it.second;
            if (*block == *ii )
         }
    }*/


    for (auto it : icall_args) {
        ArmsBasicBlock *block = it.first;
        int args = it.second;

        

        /* do not print blocks that end with a syscall */
        if (block->has_syscall()) continue;

        fprintf(fp,"%p = %d (%s.%d) ", (void *) block->get_last_insn_address(), args, f->getMangledName().c_str(),i);
        
        #ifdef STRATEGY_WIDTH
        auto search = arg_width.find(block);
        if (search != arg_width.end())
        {
            std::vector<uint16_t> icall_arg_width = search->second;
            for (auto elem : icall_arg_width)
            {
                fprintf(fp, "%d ", elem);
            }
        }
        #endif

        #ifdef STATISTICS
        auto p = icallpointer.find(block);
        if ( p != icallpointer.end())
        {
            std::vector<int> icall_pointer = p->second;
            int mycount = std::count(icall_pointer.begin(),icall_pointer.end(),0);
            if (mycount < icall_pointer.size())
            {
                fprintf(fp,"PointerArg{");
                for (auto elem:icall_pointer)
                {
                    if (elem)
                        fprintf(fp,"%d,",elem);
                }
                fprintf(fp,"} ");
            }
           
        }


        auto x = icallxor.find(block);
        if ( x != icallxor.end())
        {
            std::vector<int> icall_xor = x->second;
            int mycount = std::count(icall_xor.begin(),icall_xor.end(),0);
            if (mycount < icall_xor.size())
            {
                fprintf(fp,"Xor{");
                for (auto elem:icall_xor)
                {
                    if (elem)
                        fprintf(fp,"%d,",elem);
                }
                fprintf(fp,"} ");
            }
           
        }


        auto imm = icallimm.find(block);
        if ( imm != icallimm.end())
        {
            std::vector<int> icall_imm = imm->second;
            
            int mycount = std::count(icall_imm.begin(),icall_imm.end(),0);
            if (mycount < icall_imm.size())
            {
                fprintf(fp,"ImmArg{");
                for (auto elem:icall_imm)
                {
                    if (elem)
                        fprintf(fp,"%d,",elem);
                }
                fprintf(fp,"} ");
            }
            
           
        }


        auto icall13_p = icall13.find(block);
        if ( icall13_p != icall13.end())
        {
            std::vector<int> icall_13 = icall13_p->second;
            
            int mycount = std::count(icall_13.begin(),icall_13.end(),0);
            if (mycount < icall_13.size())
            {
                fprintf(fp,"13Arg{");
                for (auto elem:icall_13)
                {
                    if (elem)
                        fprintf(fp,"%d,",elem);
                }
                fprintf(fp,"} ");
            }
           
        }

        auto icall36_p = icall36.find(block);
        if ( icall36_p != icall36.end())
        {
            std::vector<int> icall_36 = icall36_p->second;
            //if (icall_36.size() != 0)
            int mycount = std::count(icall_36.begin(),icall_36.end(),0);
            if (mycount < icall_36.size())
            {
                fprintf(fp,"36Arg{");
                for (auto elem:icall_36)
                {
                    if (elem)
                        fprintf(fp,"%d,",elem);
                }
                fprintf(fp,"} ");
            }
           
        }

        auto icallwrapper_p = icallwrapper.find(block);
        if ( icallwrapper_p != icallwrapper.end())
        {
            int icall_wrapper = icallwrapper_p->second;
            if (icall_wrapper == 1) 
            {
                fprintf(fp, "Icall ");
            }
            else if (icall_wrapper == 2)
                fprintf(fp, "Dcall ");
           
        }

        auto icallbet_p = icallbet.find(block);
        if ( icallbet_p != icallbet.end())
        {
            int icall_bet = icallbet_p->second;
            printf("icall_bet %d\n",icall_bet);
            if (icall_bet) 
            {
                fprintf(fp, "bet");
            }
           
        }
        #endif


        fprintf(fp,"\n");
        fprintf(stderr,"finished icall setting at pass\n");
        
        i++;



        /*if (block->get_read_rax()){
            auto t = std::make_tuple(block->get_start_address(),block->get_last_insn_address(), args,true,ret_begin,ret_end);
            icall_info.push_back(t);

        }
        else
        {
            auto t = std::make_tuple(block->get_start_address(),block->get_last_insn_address(), args,false,ret_begin,ret_end);
            icall_info.push_back(t);

        }*/

    }
    return 0;
}



static int print_plts(ArmsFunction *f, void *arg) {
    if (f->is_plt()) {

        fprintf(fp,"%p = %s\n", (void *)f->get_base_addr(),f->get_name().c_str());

    }
    return 0;
}

static int print_nonvoids(ArmsFunction *f, void *arg) {
    if(f->is_plt() || f->is_lib_dummy()) return 0;

    if (f->get_write_rax()) {
        fprintf(fp,"%p = %s\n", (void *)f->get_base_addr(),f->getMangledName().c_str());
    }
    return 0;
}

static int print_nonvoidicalls(ArmsFunction*f, void *arg) {
    std::map<ArmsBasicBlock *, int> icall_args = f->get_icall_args();
    int i = 0;
    for (auto it : icall_args) {
        ArmsBasicBlock *block = it.first;
        int args = it.second;

        /* skip syscalls */
        if (block->has_syscall()) continue;

        if (block->get_read_rax()) {
            fprintf(fp,"%p = %s.%d\n", (void *) block->get_last_insn_address(), f->getMangledName().c_str(),i);
        }
        i++;
    }
    return 0;
}

static int print_goals(ArmsFunction *f, void *arg) {
    std::map<ArmsBasicBlock *, int> icall_args = f->get_icall_args();
    
    
    int i = 0;
    for (auto it : icall_args) {
        ArmsBasicBlock *block = it.first;
        int args = it.second;

        /* skip syscalls */
        if (block->has_syscall()) continue;

        if (args == 0) continue;

        std::set<ArmsFunction*> dependencies = block->get_dependencies();
        for (auto it  = dependencies.begin();
                  it != dependencies.end();
                  it++) {
            ArmsFunction *dep = *it;
            fprintf(fp, "%p = %s.%d -> %p = %s\n",
                    (void *) block->get_last_insn_address(), f->getMangledName().c_str(), i,
                    (void *) dep->get_base_addr(), dep->getMangledName().c_str() );
        }

        i++;
    }
    return 0;
}




void getParams(BPatch_image *image, BPatch_addressSpace *as, CFG *cfg,std::vector<std::vector<unsigned long>> data_info) {

    ArmsLiveness alive;
    alive.set_bpatch_image(image);
    /*if (cfg->foreach_function(ArmsLiveness::parse_functions, &alive) < 0) {
        fcfiPassLog("Could not analyze functions");
        return;
    }*/
    //revised by yanlin
    if (cfg->foreach_function_2(ArmsLiveness::parse_functions, &alive, data_info) < 0) {
        fcfiPassLog("Could not analyze functions");
        return;
    } 

    if (cfg->foreach_function(process_vararg_function, &alive) < 0) {
        fcfiPassLog("Could not analyze functions");
        return;
    }
    if (cfg->foreach_function(process_function, &alive) < 0) {
        fcfiPassLog("Could not analyze functions");
        return;
    }

    //added by yanlin
    /*#ifdef FOLLOW_DIRECT_CALL
    if (cfg->foreach_function(parse_functions_second_time,&alive) < 0){
        fcfiPassLog("Could not analyze functions");
        return;
    }
    #endif*/
   
    if (cfg->foreach_function(process_function_callsites, &alive) < 0) {
        fcfiPassLog("Could not analyze functions");
        return;
    }


}


std::map<string, std::set<void *> > getATs(string filename) {
    std::map<string, std::set<void *> > result;
    string libname;
    void *offset;

    std::ifstream infile(filename);
    while (infile >> libname >> offset) {
        result[libname].insert(offset);
    }

    return result;
}


namespace {

  class FCFIPass : public ModulePass {

    public:
        static char ID;
        FCFIPass() : ModulePass(ID) {}

        virtual bool runOnModule(void *M) {
            BPatch_addressSpace *as = (BPatch_addressSpace*) M;
            bool isBinEdit = dynamic_cast<BPatch_binaryEdit*>(as) != NULL;

            if (isBinEdit) fcfiPassLog("Running (binary edit)...");
            else           fcfiPassLog("Running (runtime)...");

            fcfiPassLog("Command-line arguments given (opt*): '" << optAT.getValue() << "'\n");


            fcfiPassLog("Reading AT functions...");
            std::map<string, std::set<void*> > at_funcs = getATs(optAT.getValue());

            BPatch_image *image = as->getImage();

            std::vector<BPatch_object *> objs;
            image->getObjects(objs);


            DICFG *cfg;

            std::vector<Unused> unused;
            unused_p = &unused;

            fcfiPassLog("Performing static analysis on objects...");

            /* Loop over all modules (shared libraries) */
          //for (unsigned i = 0; i < objs.size(); i++) {
            for (unsigned i = 0; i < 1; i++) {
                fcfiPassLog("process object file");
                string pathname = objs[i]->pathName();
                string objname  = objs[i]->name();

                if(strncmp(objname.c_str(),"libdyninstAPI_RT.so",19) == 0) { continue; }
                if(strncmp(objname.c_str(),"libm.so",7) == 0) { continue; }
                if(strncmp(objname.c_str(),"libicui18n.so",13) == 0) { continue; }
                if(strncmp(objname.c_str(),"libv8.so",8) == 0) { continue; }
                if(strncmp(objname.c_str(),"libicuuc.so",11) == 0) { continue; }

                char output[512];
                cfg = dyninst_build_cfg(as, i);
                sprintf(output,"%s.%s",optBinfo.getValue().c_str(),objname.c_str());
                fp = fopen(output,"w");
                fprintf(fp,"Object: %s\n", objname.c_str());

                fprintf(stderr,"object[%d] = %s > %s\n", i, pathname.c_str(), output);

                if(!cfg) {
                  fcfiPassLog("CFG generation failed");
                  return false;
                }

               // cfg->print_cfg();
                std::map<address_t,ArmsFunction *> tail_func = cfg->get_tail_functions();
                tail_blocks = cfg->get_tail_blocks();
                all_funcs = cfg->get_functions();

                fprintf(fp,"Functions: %lu\n", cfg->count_functions());
                std::cout <<"get data info \n";

                std::vector<std::vector<unsigned long>> data_info = cfg->dataInfo;

                
                //getParams(image, as, cfg);
                //revised by yankin
                std::cout <<"getParams \n";
                getParams(image, as, cfg,data_info);
                /*if (icall_info->size() == 0)
                {
                    fprintf(fp,"***\n");
                }
                else
                    fprintf(fp,"****%lu\n",icall_info->size());*/

                //fprintf(fp,"****");


                fprintf(fp,"\n[varargs]\n");
                if (cfg->foreach_function(print_variadics, &at_funcs[objname]) < 0) {
                    fcfiPassLog("Could not print variadic functions");
                }
                fprintf(fp,"\n[args]\n");
                if (cfg->foreach_function(print_regulars, &at_funcs[objname]) < 0) {
                    fcfiPassLog("Could not print regular functions");
                }
                fprintf(fp,"\n[icall-args]\n");
                if (cfg->foreach_function(print_icalls, &at_funcs[objname]) < 0) {
                    fcfiPassLog("Could not print indirect call argument info");
                }
                fprintf(fp,"\n[plts]\n");
                if (cfg->foreach_function(print_plts, NULL) < 0) {
                    fcfiPassLog("Could not print PLT stubs");
                }
                fprintf(fp,"\n[disas-errors]\n");
                if (cfg->foreach_function(print_disas_errs, NULL) < 0) {
                    fcfiPassLog("Could not print disassembly errors");
                }
                fprintf(fp,"\n[non-voids]\n");
                if (cfg->foreach_function(print_nonvoids, NULL) < 0) {
                    fcfiPassLog("Could not print nonvoids");
                }
                fprintf(fp,"\n[non-void-icalls]\n");
                if (cfg->foreach_function(print_nonvoidicalls, NULL) < 0) {
                    fcfiPassLog("Could not print non void icalls");
                }
                fprintf(fp,"\n[prof-goals]\n");
                if (cfg->foreach_function(print_goals, NULL) < 0) {
                    fcfiPassLog("Could not print profiling goals");
                }


				/*
                cout << "***"<< icall_info.size()<<endl;
                FILE *fp_count;
                char output_count[512];
                sprintf(output_count,"%s_count_func.txt", objname.c_str());
                fp_count = fopen(output_count,"w");


                FILE *fp_cfi;
                char output_cfi[512];
                sprintf(output_cfi,"%s_cfi.txt", objname.c_str());
                fp_cfi = fopen(output_cfi,"w");

                all_CFG = cfg->print_cfg();

                for(std::vector<std::tuple<address_t, address_t,int, bool,address_t,address_t>>::iterator it_call = icall_info.begin(); it_call != icall_info.end(); it_call++)
                {
                    size_t count  = 0;
                    for (std::vector<std::tuple<address_t, address_t, int, bool,address_t,address_t>>::iterator it_func = func_info.begin(); it_func != func_info.end(); it_func++){
                        if (( get<2>(*it_call) >= get<2>(*it_func) ) && (get<3>(*it_call) == get<3>(*it_func) == true || get<3>(*it_call) == false))
                        {
                            count++;

                            //CFI[get<0>(*it_call)].push_back(get<0>(*it_func));
                            all_CFG[std::make_tuple(1,get<0>(*it_call),get<1>(*it_call))].push_back(make_pair(get<0>(*it_func),get<1>(*it_func)));
                            if (get<4>(*it_func) !=0 &&  get<5>(*it_func) !=0){

                            if ( all_CFG.find(std::make_tuple(1,get<4>(*it_func),get<5>(*it_func)))!= all_CFG.end())
                            {
                                cout << hex <<get<3>(*it_func)<<endl;
                               
                                all_CFG[std::make_tuple(0,get<4>(*it_func),get<5>(*it_func))].push_back(make_pair(get<4>(*it_call),get<5>(*it_call)));
                            }
                            else {
                                //all_CFG[make_pair(0,get<3>(*it_func))].push_back(get<3>(*it_call));
                                all_CFG[std::make_tuple(0,get<4>(*it_func),get<5>(*it_func))].push_back(make_pair(get<4>(*it_call),get<5>(*it_call)));
                            }
                            //fprintf(fp_cfi,"%d <%x %x> ",get<0>(*it_call),get<1>(*it_call),);


                            //cout << "indirect call: " <<hex<< get<0>(*it_call) << " "<<hex<<get<0>(*it_func)<<endl;
                            //cout << "ret for indirect call:  " <<hex<<get<4>(*it_func) << " "<<hex<<get<4>(*it_call)<<endl;
                        }
                        }

                    }
                     fprintf(fp_count, "%d %p\n", count, get<0>(*it_call));

                }
                fclose(fp_count);*/

                /*for (std::vector<std::tuple<address_t, int, bool,address_t>>::iterator it_func = func_info.begin(); it_func != func_info.end(); it_func++){
                    //cout<<"func for indirect call "<<hex<<get<0>(*it_func)<<endl;
                    size_t count = 0;
                    for(std::vector<std::tuple<address_t, int, bool,address_t>>::iterator it_call = icall_info.begin(); it_call != icall_info.end(); it_call++){
                        if (( get<1>(*it_call) >= get<1>(*it_func) ) && get<2>(*it_call) == get<2>(*it_func) )
                        {
                            CFI[get<0>(*it_func)].push_back(get<0>(*it_call));
                            CFI[get<3>(*it_call)].push_back(get<3>(*it_func));
                            //cout<<hex<<get<0>(*it_call)<<endl;
                            count++;

                        }
                    }
                    fprintf(fp_count, "%d %p\n", count, get<0>(*it_func));
                }
                fclose(fp_count);*/


                //CFI = cfg->print_cfg();
                /*for(std::map<std::pair<int, address_t>,std::vector<address_t>>::iterator ii=all_CFG.begin(); ii!=all_CFG.end(); ++ii){
                    fprintf(fp_cfi,"%d %x ",(*ii).first.first,(*ii).first.second);
                    //cout << (*ii).first << ": ";
                    //cout <<"******"<<" "<<endl;
                    std::vector <address_t> inVect = (*ii).second;
                    for (unsigned j=0; j<inVect.size(); j++){
                        fprintf(fp_cfi,"%x ",inVect[j]);
                        //cout << inVect[j] << " ";
                    }
                    fprintf(fp_cfi,"\n");
                    //cout << endl;
                }*/
                /*for(std::map<std::tuple<int, address_t,address_t>,std::vector<std::pair<address_t,address_t>>>::iterator ii=all_CFG.begin(); ii!=all_CFG.end(); ++ii)
                {
                    fprintf(fp_cfi,"%d,%x %x,",get<0>((*ii).first),get<1>((*ii).first),get<2>((*ii).first));
                    for (std::vector< std::pair<address_t,address_t>>::iterator it = (*ii).second.begin(); it != (*ii).second.end();++it)
                    {
                        fprintf(fp_cfi,"%x %x,",(*it).first,(*it).second);

                    }
                   

                    fprintf(fp_cfi,"\n");
                }
                fclose(fp_cfi);

                fclose(fp);*/
            }


            /*
            fcfiPassLog("Functions that were never called directly:");
            for (auto u : unused) {
                fprintf(stderr,"- [%s] %p: %s\n", u.libname.c_str(),
                                                  u.faddr,
                                                  u.fname.c_str());
            }
            */


if (optUnused.getValue()) {
            fcfiPassLog("Searching for 'intermodulair' calls to unused functions...");

            for (unsigned i = objs.size(); i-- > 0; ) {
                string pathname = objs[i]->pathName();
                string objname  = objs[i]->name();

                if(strncmp(objname.c_str(),"libdyninstAPI_RT.so",19) == 0) continue;

                cfg = dyninst_build_cfg(as, i);
                if(!cfg) {
                  fcfiPassLog("CFG generation failed");
                  return false;
                }

                fcfiPassLog("- " << objname);
                if (cfg->foreach_function(process_unused_function, NULL) < 0) {
                    fcfiPassLog("Could not analyze functions");
                    return false;
                }
            }
}


            for (unsigned i = 0; i < objs.size(); i++) {
                string pathname = objs[i]->pathName();
                string objname  = objs[i]->name();

                if(strncmp(objname.c_str(),"libdyninstAPI_RT.so",19) == 0) continue;

                char output[512];
                sprintf(output,"%s.%s",optBinfo.getValue().c_str(),objname.c_str());
                fp = fopen(output,"a");

                fprintf(fp,"\n[unused]\n");

if (optUnused.getValue()) {
                for (auto u : unused) {
                    if (u.libname == pathname) {
                        if (!u.intermodulair) {
//                          fprintf(fp,"%p = %s\n", u.faddr, u.fname.c_str());
                            for (auto it : u.callsites) {
                                fprintf(fp,"%p = %s\n", it, u.fname.c_str());
                            }

                        }
                    }
                }
}
                fprintf(fp,"\n[done]\n");
                fclose(fp);
            }


            fcfiPassLog("Done...");
            fprintf(stderr, "[+] Done...\n");

            return false;
        }
  };
}

char FCFIPass::ID = 0;
RegisterPass<FCFIPass> MP("fcfi_pass", "FCFI Pass");

