KULFI
=====
#### Version: beta 2 version
## Introduction

Kontrollable Utah LLVM Fault Injector (KULFI) tool is an instruction level fault injector which is capable of injecting random single bit errors at instruction level. It supports both dynamic and static error injection techniques. In case of static error injection, the fault site is randomly selected before the program execution. In case of dynamic error injection, fault site is randomly selected during program execution. KULFI allows finer control over error injection by providing options which could be defined by user. E.g., user could define probablity of the fault occurence, byte position where error could be injected, distinguish whether fault should be injected into pointer register or data register etc.  KULFI utilizes [LLVM](http://llvm.org/) Compiler Infrastructure. This tool is owned by [Gauss Research Group](http://www.cs.utah.edu/formal_verification/) at [School of Computing](http://www.cs.utah.edu/), [University of Utah](http://www.utah.edu/), Salt Lake City, USA. If you have any tool related queries, join our <a href="https://groups.google.com/d/forum/kulfi-dev"> mail list</a> and send your queries to: <a href="mailto:kulfi-dev@googlegroups.com"> KULFI developer's list</a>.  <br><br> Copyright Information: This code is available under The University of Illinois/NCSA Open Source License (NCSA).Please refer to the <a href="http://opensource.org/licenses/NCSA">link</a> for more details.

## List of Contributors
1. <a href="mailto:vcsharma@cs.utah.edu">Vishal Sharma</a> (Phd Student at School of Computing, University of Utah)
2. <a href="mailto:haran@cs.utah.edu">Arvind Haran</a> (Masters student at School of Computing, University of Utah)
3. <a href="mailto:suichen6@gmail.com">Sui Chen</a> (Phd Student at Department of Computer Science, Louisiana State University)

## Prerequisite
- [LLVM version 3.2](http://llvm.org/releases/3.2/docs/ReleaseNotes.html)
- [Clang version 3.2](http://llvm.org/releases/download.html#3.2)
- Python 2.5+ ([2.7.3](http://www.python.org/getit/releases/2.7.3/) recommended)
- Unix like operating system (Ubuntu, Debian) - The current version of KULFI is tested on Ubuntu 12.04 LTS

## Installation
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
- Please refer to the [link] (http://llvm.org/docs/WritingAnLLVMPass.html#setting-up-the-build-environment) to get details on how to set up the build environment to compile an LLVM pass.
- Alternatively, you could use pre-compiled binary - faults.so, located at KULFI/bin.

## Steps to Execute

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
    
    $ opt -load <path-to-faults.so>/faults.so [-staticfault|-dynfault] [-ef N] [-tf N] [-b N] [-de 0/1] [-pe 0/1] [-ijo 0/1] 
      [-pfs 0/1] [-fn "func_name"]
    < Final.bc > Final-corrupt.bc
    Here "Final-corrupt.bc" is the modified LLVM bit code with the required code instrumention to inject 
    static/dynamic fault.
Refer to the [link](http://llvm.org/docs/WritingAnLLVMPass.html#running-a-pass-with-opt) to know how to run an LLVM pass using opt. 

#### Step 5: Execute
    Use lli to execute the LLVM bitcodes "Final.bc" and "Final-corrupt.bc" as mentioned below:
    $ lli Final.bc > Final.out
    $ lli Final-corrupt.bc > Final-corrupt.out
    "Final.out" and "Final-corrupt.out" contains the program output with and without faults injected 
    respectively.
For more details on how to execute LLVM bitcode, refer to the [link](http://llvm.org/docs/GettingStarted.html#an-example-using-the-llvm-tool-chain).  

    
## Command Line Options

    -staticfault   - to select static fault injection 
    
    -dynfault      - to select dynamic fault injection
    
    -ef            - [input range: >=1] [default input: 100] specifies the expected 
                     number of faults to be injected. It is used in probbality cal-
                     culation.
                    
    -tf            - [input range: >=1] [default input: 100] specifies the total nu-
                     mber of fault sites. It is used in the probablity calculation.
                     
    -b             - [input range: 0-7] [default input: random] specifies which byte 
                     of the data register to consider for fault injection.
                     
    -de            - [input: 0/1] [default input: 1] 0: doesn't inject error into data 
                     reg, 1: inject error into data reg
                     
    -pe            - [input: 0/1] [default input: 0] 0: doesn't inject error into pointer 
                     reg, 1: inject error into pointer reg
                     
    -ijo           - [input: 0/1] [default input: 1] 1: exits after injecting first 
                     fault. 0: considers all possible fault sites for fault injection

    -fn            - [input: string] [default input: None]: injects error only into the
                     function(s) pass through this flag. Ex: -fn "func1 func2". If this
                     flag is not used then all possible function(s) are considered for
                     fault injection.

    -pfs           - [input: 0/1] [default input: 0] 1: enables fault site printing mode.
                     In this mode all possible fault sites are printed and no errors are
                     injected. 0: disable fault site printing mode. To inject errors make 
                     sure that this mode is disabled.
                     
## Examples
Refer to KULFI/example directory. We have different sorting algorithms which could be tried 
for error injection. Below is an example of error injection for bubblesort implementation.

    $ cd to KULFI/examples/sorting/

    $ python sorting.py <ARGS>
      Arg1: <source_file>            	    type: string
      Arg2: <Corrupt.c file>        	    type: string
      Arg3: <faults.so file>        	    type: string
      Arg4: <iteration>	  	    	        type: integer
      Arg5: <byte_position>	  	            type: integer
      Arg6: <expected fault count>  	    type: integer
      Arg7: <total fault count>             type: integer
      Arg8: <inject_once flag>              type: bool(0/1)
      Arg9: <static_fault/dynamic_fault>    type: bool(0/1)
      Arg10: <inject_pointer_error>  	    type: bool(0/1)
      Arg11: <inject_data_error>  	        type: bool(0/1)
      Arg12: <print_fault_site>  	        type: bool(0/1)
      Arg13: <function_name>  	            type: string
 
Sample Command Line to execute

    $ python sorting.py bubblesort/bubblesort.c ../../../src/other/Corrupt.c ../../../bin/faults.so 2 0 10 100 1 1 0 1 0 "bubbleSort"

    $ python sorting.py --help :prints the help message

This instructs KULFI to look for bubblesort.c and run 2 iterations of the source code after fault injection. The specifics of the fault injection being: A dynamic fault with fault probability 12% injected only once in the data registers.
The results of the fault injection are categorized into silent data corruptions, benign faults, out of bound accesses and segmentation faults. The fault statistics are available in bubblesort/stats.txt after execution.

To clean the directory, type:

    $ python sorting.py clean
    

## Known Bugs/Limitations
- Only C is supported by KULFI. C++ is currently not supported.


## List of Changes
Beta 2 release
- Fixes issue #5: Added command line option "-pfs" to print fault sites
- Fixes issue #3: Added command line option "-fn" to support selecting functions for error injection from command line
- Fixes issue #7: Added support for floating-point data type
- Fixes issue #4: "Add support for automatically converting to a valid range if the byte pos entered through -b flag is out-of-bound bug" 
- Fixes issue #8: Tweaked the example python file to accomodate the additional command line options and optimizations to remove dependency on local copies of main src files.
- Fixes issue #9: Changed the default value of "-b" flag from 0 to random


