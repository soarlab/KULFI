KULFI
=====

##Introduction

Kontrollable Utah LLVM Fault Injector (KULFI) tool is an instruction level fault injector which is capable of injecting random single bit errors at instruction level. It supports both dynamic and static error injection techniques. In case of static error injection, fault site is randomly selected before the program execution. In case of dynamic error injection, fault site is randomly selected during program execution. KULFI allows finer control over error injection by providing options which could be defined by user. E.g., user could define probablity of the fault occurence, byte position where error could be injected, distinguish whether fault should be injected into pointer register or data register etc.  KULFI utilizes [LLVM](http://llvm.org/) Compiler Infrastructure. This tool is owned by [Gauss Research Group](http://www.cs.utah.edu/formal_verification/) at [School of Computing](http://www.cs.utah.edu/), [University of Utah](http://www.utah.edu/), Salt Lake City, USA. If you have any tool related queries, please send it to: <a href="mailto:vcsharma@cs.utah.edu">Vishal Sharma</a> / <a href="mailto:haran@cs.utah.edu"> Arvind Haran</a>.  <br><br> Copyright Information: This code is available under The University of Illinois/NCSA Open Source License (NCSA).Please refer to the <a href="http://opensource.org/licenses/NCSA">link</a> for more details.

##Prerequisite
- [LLVM version 3.2](http://llvm.org/releases/3.2/docs/ReleaseNotes.html)
- [Clang version 3.2](http://llvm.org/releases/download.html#3.2)
- Python 2.5+ ([2.7.3](http://www.python.org/getit/releases/2.7.3/) recommended)
- Unix like operating system (Ubuntu, Debian) - The current version of KULFI is tested on Ubuntu 12.04 LTS

##Installation
##### Step 1: Download source code
    $ cd where-you-want-kulfi-source-to-live  
    $ git clone https://github.com/vcsharma/KULFI.git
    
##### Step 2: Build
    $ cd llvm-3.2-build-dir/lib/Transforms
    $ mkdir Faults
    $ cd Faults 
    $ cp <kulfi-source-dir>/KULFI/src/main/* ./        
    $ [sudo] make
    
##### Step 3: Install
    $ [sudo] make install
    
##### Note: 
Please refer to the [link] (http://llvm.org/docs/WritingAnLLVMPass.html#setting-up-the-build-environment) to get details on how to set up the build environment to compile an LLVM pass.

##Steps to Execute
##### Step 1: Compile "Corrupt.c" at KULFI/src/other
    Before running the fault pass, first compile the Corrupt.c using below command:
    $ clang -O1 -emit-llvm Corrupt.c -c -o Corrupt.bc
    
##### Step 2: Compile taget source code
    Now compile your target C source code (say Sample.c) using below command:
    $ clang -O1 -emit-llvm Sample.c -c -o Sample.bc

##### Step 3: Link "Corrupt.bc" to target bit code
    Now link the above two file as mentioned below:
    $ llvm-link Corrupt.bc Sample.bc -o Final.bc

##### Step 4: Inject fault(s)!
Now run the fault pass on "Final.bc" using below guideline. Refer to the "Command Line Options" section to get details about supported flags.
    
    $ opt -load <path-to-faults.so>/faults.so [-staticfault|-dynfault] [-fp N] [-b N] [-de 0/1] [-pe 0/1] [-ijo 0/1]
    
    
##### Note: 
Refer to the [link](http://llvm.org/docs/WritingAnLLVMPass.html#running-a-pass-with-opt) to know how to run an LLVM pass using opt
    

##Command Line Options

    -staticfault   - to select static fault injection 
    
    -dynfault      - to select dynamic fault injection
    
    -fp            - [input range: 1-100] [default input: 100] specifies the probablity 
                     of injecting the fault
                     
    -b             - [input range: 0-7] [default input: 0] specifies which byte of the 
                     data register to consider for fault injection.
                     
    -de            - [input: 0/1] [default input: 1] 0: doesn't inject error into data 
                     reg, 1: inject error into data reg
                     
    -pe            - [input: 0/1] [default input: 1] 0: doesn't inject error into pointer 
                     reg, 1: inject error into pointer reg
                     
    -ijo           - [input: 0/1] [default input: 1] 1: exits after injecting first fault
                     0: considers all possible fault sites for fault injection

## Additional Notes
- None
