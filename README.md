KULFI
=====

##Introduction

Kontrollable Utah LLVM Fault Injector (KULFI) tool is an instruction level fault injector which is capable of injecting random single bit errors at instruction level. It supports both dynamic and static error injection techniques. In case of static error injection, fault site is randomly selected before the program execution. In case of dynamic error injection, fault site is randomly selected during program execution. KULFI utilizes [LLVM](http://llvm.org/) Compiler Infrastructure. This tool is owned by [Gauss Research Group](http://www.cs.utah.edu/formal_verification/) at [School of Computing](http://www.cs.utah.edu/), [University of Utah](http://www.utah.edu/), Salt Lake City, USA. If you have any tool related queries, please send it to: <a href="mailto:vcsharma@cs.utah.edu">Vishal Sharma</a> / <a href="mailto:haran@cs.utah.edu"> Arvind Haran</a>.  <br><br> Copyright Information: This code is available under The University of Illinois/NCSA Open Source License (NCSA).Please refer to the <a href="http://opensource.org/licenses/NCSA">link</a> for more details.

##Prerequisite
- [LLVM version 3.2](http://llvm.org/releases/3.2/docs/ReleaseNotes.html)
- [Clang version 3.2](http://llvm.org/releases/download.html#3.2)
- Python 2.5+ ([2.7.3](http://www.python.org/getit/releases/2.7.3/) recommended)
- Unix like operating system (Ubuntu, Debian)

##Installation
##### Step 1.
    cd where-you-want-kulfi-source-to-live  
    git clone https://github.com/gaussers/KULFI.git
    
##### Step 2.
    cd KULFI/src  
    make
    make install
    
##### Note: 
Please refer to the [link] (http://llvm.org/docs/WritingAnLLVMPass.html#setting-up-the-build-environment) to get details on how to set up the build environment to compile an LLVM pass.

##Steps to Execute


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


