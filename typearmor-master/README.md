
This is the open-source component of our paper "When Function Signature Recovery Meets Compiler Optimization", published in IEEE Security & Privacy (S&P) 2021. It allows you to retrieve argument count information for callees and callsites of compiled C/C++ applications using the improved policy metioned in the paper.  


# Disclaimer
If, for some weird reason, you think running this code broke your device, you get to keep both pieces.

# Installation
To build the static analysis pass, we first need to build Dyninst. Although we used an older version for our paper, the current latest version (9.3.1) should work just fine. 

Note that the following was tested in a Ubuntu Desktop 18.04 LTS. 

First install some packages:

    sudo apt-get install build-essential cmake 
    sudo apt-get install libboost-all-dev libelf-dev libiberty-dev

Next, download and build Dyninst. 

    cd
    wget https://github.com/dyninst/dyninst/archive/v9.3.1.tar.gz
    tar -zxvf v9.3.1.tar.gz
    cd dyninst-9.3.1
    mkdir install
    cd install
    cmake .. -DCMAKE_INSTALL_PREFIX=`pwd`
    make -j2
    make install

Next, download and build TypeArmor:

    cd 
    git clone git@github.com:vusec/typearmor.git
    cd typearmor
    # update DYNINST_ROOT in ./envsetup.sh
    . build_envsetup
    cd static
    make
    make install
    cd ..
    cd di-opt
    make
    make install

You can now run TypeArmor on any given binary. The repository is shipped with the binaries used in our S&P paper:
    
    cd
    cd server-bins
    ../run-ta-static.sh ./nginx

This will generate new binary info file(s) in `../out/binfo.*`. Log output will be pushed to `./ta.log`.


# binfo format

Each `binfo.*` file contains different sections:

* *[varargs]*
  Variadic functions:

    ```<address> = <min consumed argccount> (<function symbol>) ```

* *[args]*
  Regular (non-variadic) functions:

    ```<address> = <min consumed argcount> (<function symbol>) width for each argument reg_bitmap possible compilation```

* *[icall-args]*
  Indirect callsites:

    ```<address> = <max prepared argcount> (<function symbol>.<callsite index in function>) width for each argument reg_bitmap possible compilation```

* *[plts]*
  PLT entries.

* *[disas-errors]*
  Disassembly errors.

* *[non-voids]*
  Functions that seem to be of type non-void (i.e., they write RAX):

    ```<address> = <function symbol>```

* *[prof-goals]*
  Indirect calls that could benefit from a profiling sessions:
  
    ```<call address> = <function symbol>.<index> -> <address of function from which we could not backtrack> = <target_function_symbol>```

* *[unused]*
  Function is never used.

* *[done]*
  Marker that indicates the end of the binfo.
  
#notation for possible compilation
* *readRDX*
  functions which read %rdx after a call instruction
  
* *read63*
  functions which read 64 bit argument register, but the actual argument register is 32-bit, including lea and Push
	
* *Icall*
  Indirect caller in wrapper function and there is no direct caller for this wrapper function
	
* *Dcall*
  Indirect caller in wrapper function and there are direct callers for this wrapper function

* *ImmArg*
  Indirect callers whose passed arguments are immediate values

* *PointerArg*
  Indirect callers whose passed arguments are pointers points to .data and .text sections
  
* *Xor*
  Indirect callers whose arguments are passed using xor instructions

* *13Arg*
  Indirect caller whose arguments read 16-bit to 32-bit register

* *36Arg*
  Indirect call whose arguments read 32-bit to 64-bit register


