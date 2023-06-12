#!/bin/bash

export DYNINST_ROOT=/home/yanlin/toolchain/dyninst-9.3.1
export DYNINST_LIB=$DYNINST_ROOT/install/lib
export DYNINSTAPI_RT_LIB=$DYNINST_LIB/libdyninstAPI_RT.so
export LD_LIBRARY_PATH=$DYNINST_LIB:$LD_LIBRARY_PATH

export TIGRESS_HOME=/home/yanlin/my-projects/obfuscation-arg/tigress-3.1-bin/tigress/3.1
export PATH=TIGRESS_HOME:$PATH