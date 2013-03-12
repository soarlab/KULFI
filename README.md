KULFI
=====

##Introduction

Kontrollable Utah LLVM Fault Injector (KULFI) tool is an instruction level fault injector which is capable of injecting random single bit errors at instruction level. It supports both dynamic and static error injection techniques. KULFI utilizes <a href="http://llvm.org/">LLVM</a> Compiler Infrastructure. This tool is owned by <a href="http://www.cs.utah.edu/formal_verification/">Gauss Research Group</a> at <a href="http://www.cs.utah.edu/">School of Computing</a>, <a href="http://www.utah.edu/">University of Utah</a>, Salt Lake City, USA. If you have any tool related queries, please send it to: <a href="mailto:vcsharma@cs.utah.edu">Vishal Sharma</a> / <a href="mailto:haran@cs.utah.edu"> Arvind Haran</a>.  <br><br> Copyright Information: This code is available under The University of Illinois/NCSA Open Source License (NCSA).Please refer to the <a href="http://opensource.org/licenses/NCSA">link</a> for more details.

##Prerequisite
- [LLVM version 3.2](http://llvm.org/releases/3.2/docs/ReleaseNotes.html)
- [Clang version 3.2](http://llvm.org/releases/download.html#3.2)
- Python 2.5+ ([2.7.3](http://www.python.org/getit/releases/2.7.3/) recommended)
- Unix like operating system (Ubuntu, Debian)

##Installation
   


##Steps to Execute


##Command Line Options

    -staticfault   - to select static fault injection<br>
    -dynfault      - to select dynamic fault injection<br>
    -fp            - [input range: 1-100] [default input: 100] specifies the probablity 
                     of injecting the fault<br>
    -b             - [input range: 0-7] [default input: 0] specifies which byte of the 
                     data register to consider for fault injection.<br>
    -de            - [input: 0/1] [default input: 1] 0: doesn't inject error into data 
                     reg, 1: inject error into data reg<br>
    -pe            - [input: 0/1] [default input: 1] 0: doesn't inject error into pointer 
                     reg, 1: inject error into pointer reg<br>
    -ijo           - [input: 0/1] [default input: 1] 1: exits after injecting first fault
                     0: considers all possible fault sites for fault injection<br>


