import os,sys,random,shlex
from os.path import basename


def printstats(numseg,numbenign,numoob,numsdc,i):
	falseop = open(dirn+"/faulty_"+fname+"/"+str(i)+".out",'r') # faulty .out file
	trueop= open(dirn+"/actual_"+fname+"/"+str(i)+".out",'r') # actual .out file

	line=trueop.readline()
	s = shlex.split(line)
	for i in range(len(s)):
		s[i]=int(s[i])
	line1=falseop.readline()
	if(not line1):
		numseg+=1
		return numseg,numbenign,numoob,numsdc
	else:
		t=[]    
		t = shlex.split(line1)
		for i in range(len(t)):
			t[i]=int(t[i])
		if(len(s)==len(t)):
			flag=0
			for d in range(len(s)):
				if(t[d]!=s[d]):
					numsdc+=1
					return numseg,numbenign,numoob,numsdc
		else:
			numoob+=1
			return numseg,numbenign,numoob,numsdc

	numbenign+=1
	return numseg,numbenign,numoob,numsdc
	falseop.close()
	trueop.close()

def geninput(size):
	f=open(dirn+"/tempinput.txt",'w')
	x=[]
	f.write(str(size)+"\n")
	for i in range(1,size+1):
		y=random.randint(-50000,50000)
		while y in x:
			y=random.randint(-50000,50000)
			x.append(y)
		if(i == size):
			f.write(str(y)+"\n")
		else:
			f.write(str(y)+" ")
	f.close()
	os.system("cat "+dirn+"/tempinput.txt >> "+dirn+"/inputs.txt")

if __name__ == "__main__":
	global dirn, fname, cdirn, cfname, fdirn, ffname
	dirn = ""
	fname = ""
	cdirn = ""
	cfname = ""
	fdirn = ""
	ffname = ""	
        if(sys.argv[1]=="clean"):
		os.system("rm */*.bc */*.txt")
		os.system("rm -rf */faulty_*")
		os.system("rm -rf */actual_*")
                sys.exit()
	
	if(sys.argv[1]=="--help" or sys.argv[1]=="?" or sys.argv[1]=="-h"):
		print "\n"
		print "Execution format: python sorting.py <ARGS>"
		print "Arg1: <source_file>            	    type: string"
		print "Arg2: <Corrupt.c file>        	    type: string"		
		print "Arg3: <faults.so file>        	    type: string"		
		print "Arg4: <iteration>	  	    type: integer"		
		print "Arg5: <byte_position>	  	    type: integer"		
		print "Arg6: <expected fault count>  	    type: integer"		
		print "Arg7: <total fault count>           type: integer"		
		print "Arg8: <inject_once flag>            type: bool(0/1)"		
		print "Arg9: <static_fault/dynamic_fault>  type: bool(0/1)"		
		print "Arg10: <inject_pointer_error>  	    type: bool(0/1)"		
		print "Arg11: <inject_data_error>  	    type: bool(0/1)"		
		print "Arg12: <print_fault_site>  	    type: bool(0/1)"		
		print "Arg13: <function_name>  	   	    type: string"					
	        print "\n"
                print"Sample command line: "
		print "python sorting.py bubblesort/bubblesort.c ../../../src/other/Corrupt.c ../../../bin/faults.so 2 0 10 100 1 1 0 1 0 bubbleSort"
		print "\n"
		sys.exit()
	
	if(len(sys.argv) < 4):
		print "Invalid or insufficient argument. Type --help to get help"
		sys.exit()
        

	progname=sys.argv[1] # absolute location of bubblesort.c
        crptfile=sys.argv[2] # absolute location of Corrupt.c
	faultpass=sys.argv[3] #absolute location of faults.so 	
	numiter=int(sys.argv[4]) #number of iterations		
	byte_val=int(sys.argv[5]) #-b	
	ef=int(sys.argv[6]) #-ef		
	tf=int(sys.argv[7]) #-tf	
	injectonce=int(sys.argv[8]) #-ijo	
	injecttype=int(sys.argv[9]) #static fault or dynamic fault	
	pointerror=int(sys.argv[10]) #-pe	
	dataerror=int(sys.argv[11]) #-de
	pfs=int(sys.argv[12]) #-pfs
	fn=sys.argv[13]
	
	print(progname, numiter, ef, tf, injectonce, injecttype, pointerror, dataerror, pfs, fn)
	errflag=1
	

	if(injectonce != 0 and injectonce!=1):
		print("Enter 0 or 1 for injectonce flag")
		errflag=0
	if(injecttype != 0 and injecttype != 1):
		print("Invalid option for fault injection type. Please enter 0 for static fault 1 for dynamic fault.")
		errflag=0
	if(pointerror not in range(0,2) or dataerror not in range(0,2)):
		print("Pointer/Data error flag must be 0/1")
		errflag=0
	
	if(not errflag):
		sys.exit()

	if(not os.path.exists(progname)):
		print(progname + "not found")
		sys.exit()
	if(not os.path.exists(crptfile)):
		print(crptfile + "not found")
		sys.exit()	
	if(not os.path.exists(faultpass)):
		print(faultpass+ "not found")
		sys.exit()        
	dirn = os.path.dirname(os.path.realpath(progname))
	fname =  os.path.splitext(basename(progname))[0]
	cdirn = os.path.dirname(os.path.realpath(crptfile))
	cfname =  os.path.splitext(basename(crptfile))[0]
	fdirn = os.path.dirname(os.path.realpath(faultpass))
	ffname =  os.path.splitext(basename(faultpass))[0]
	
	print"src file name: "+ fname
	
	os.system("rm -rf "+dirn+"/faulty_*")
	os.system("rm -rf "+dirn+"/actual_*")
	os.system("mkdir "+dirn+"/faulty_"+fname+"/")
	os.system("mkdir "+dirn+"/actual_"+fname+"/")	

	os.system("clang -O1 -emit-llvm "+crptfile+" -c -o "+dirn+"/"+cfname+".bc")
	os.system("clang -O1 -emit-llvm "+progname+" -c -o "+dirn+"/"+fname+".bc")	
	os.system("llvm-link "+dirn+"/"+cfname+".bc "+dirn+"/"+fname+".bc " + " -o "+dirn+"/linked.bc")
	
	
	if(injecttype):
		os.system("opt -load "+faultpass+" -dynfault -ef "+str(ef)+" -tf "+str(tf)+" -pe "+str(pointerror)+" -de "+str(dataerror)+" -b "+str(byte_val)+" -ijo "+str(injectonce)+" -pfs "+str(pfs)+" -fn "+fn+" < "+dirn+"/linked.bc > "+dirn+"/final.bc")
	else:
		os.system("opt -load "+faultpass+" -staticfault -ef "+str(ef)+" -tf "+str(tf)+ "-pe "+str(pointerror)+" -de "+str(dataerror)+" -b 0 -ijo "+str(injectonce)+" < "+dirn+"/linked.bc > "+dirn+"/final.bc")

	stats=open(dirn+"/stats.txt","w")
	segiters=open(dirn+"/segiter.txt","w")
	hangiters=open(dirn+"/hangiter.txt","w")
	numseg=numoob=numbenign=numsdc=0

	for i in range(numiter):
		size=random.randint(2000,10000)
		geninput(size)
		print("-----------Iteration Number: "+str(i)+"--------------")
		os.system("lli "+dirn+"/"+fname+".bc "+dirn+"/tempinput.txt "+dirn+"/actual_"+fname+"/"+str(i)+".out")
		s=os.system("timeout 1000 lli "+dirn+"/final.bc "+dirn+"/tempinput.txt "+dirn+"/faulty_"+fname+"/"+str(i)+".out")

		if(s == 35584):
			numseg+=1
			segiters.write(str(i)+"\n")
			continue
		elif(s == 124):
			numseg+=1
			hangiters.write(str(i)+"\n")
			continue
		else:
			numseg,numbenign,numoob,numsdc=printstats(numseg,numbenign,numoob,numsdc,i)

	stats.write("Segmentation Faults: "+str(numseg)+" Benign Faults: "+str(numbenign)+" Out of Bounds: "+str(numoob)+" SDC: "+str(numsdc))
			
