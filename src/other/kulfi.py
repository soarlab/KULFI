import os,sys,random,shlex
def printstats(numseg,numbenign,numoob,numsdc,i):
	falseop = open("faulty_"+sys.argv[1]+"/"+str(i)+".out",'r') # faulty .out file
	trueop= open("actual_"+sys.argv[1]+"/"+str(i)+".out",'r') # actual .out file

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
	f=open('tempinput.txt','w')
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
	os.system("cat tempinput.txt >> inputs.txt")

if __name__=="__main__":
        if(sys.argv[1]=="clean"):
		os.system("rm *.bc *.txt");
		os.system("rm -rf faulty_*");
		os.system("rm -rf actual_*");
                sys.exit()

	if(len(sys.argv) !=8 or (len(sys.argv)==2 and sys.argv[1]=="--help")):
		print("Execution format: python3 kulfi.py <Source code name without extension> <number of iterations> <fault prob 0-100> <inject once 0/1> <static fault or dynamic fault 0/1> <pointer error 0/1> <data error 0/1>")
		sys.exit()

	progname=sys.argv[1]
	numiter=int(sys.argv[2])
	fprob=int(sys.argv[3])
	injectonce=int(sys.argv[4])
	injecttype=int(sys.argv[5])
	pointerror=int(sys.argv[6])
	dataerror=int(sys.argv[7])
	print(progname, numiter, fprob, injectonce, injecttype, pointerror, dataerror)
	errflag=1
	
	if(not os.path.exists(progname+".c")):
		print("Source file not in current directory")
		errflag=0
	if(fprob not in range(0,101)):
		print("Fault probability must be within 0 and 100")
		errflag=0
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

	if(os.path.exists("actual_"+sys.argv[1]+"/")):
		os.system("rm -r actual_"+sys.argv[1]+"/")
	os.system("mkdir actual_"+sys.argv[1]+"/")

	if(os.path.exists("faulty_"+sys.argv[1]+"/")):
		os.system("rm -r faulty_"+sys.argv[1]+"/")
	os.system("mkdir faulty_"+sys.argv[1]+"/")

	os.system("clang -O1 -emit-llvm "+sys.argv[1]+".c -c -o "+sys.argv[1]+".bc")
	
	if(not os.path.exists("Corrupt.c")):
		print("Corrupt.c Not found")
		sys.exit()

	os.system("clang -O1 -emit-llvm Corrupt.c -c -o Corrupt.bc")
	os.system("llvm-link Corrupt.bc "+sys.argv[1]+".bc -o linked.bc")
	
	if(injecttype):
		os.system("opt -load ./faults.so -dynfault -fp "+str(fprob)+" -pe "+str(pointerror)+" -de "+str(dataerror)+" -b 0 -ijo "+str(injectonce)+" <linked.bc> final.bc")
	else:
		os.system("opt -load ./faults.so -staticfault -fp "+str(fprob)+" -pe "+str(pointerror)+" -de "+str(dataerror)+" -b 0 -ijo "+str(injectonce)+" <linked.bc> final.bc")

	stats=open("stats.txt","w")
	segiters=open("segiter.txt","w")
	hangiters=open("hangiter.txt","w")
	numseg=numoob=numbenign=numsdc=0

	for i in range(numiter):
		size=random.randint(2000,10000)
		geninput(size)
		print("-----------Iteration Number: "+str(i)+"--------------")
		os.system("lli "+sys.argv[1]+".bc tempinput.txt actual_"+sys.argv[1]+"/"+str(i)+".out")
		s=os.system("timeout 10 lli final.bc tempinput.txt faulty_"+sys.argv[1]+"/"+str(i)+".out")

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
			
