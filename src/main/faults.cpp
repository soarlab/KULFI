/*******************************************************************************************/
/* Name        : Kontrollable Utah LLVM Fault Injector (KULFI) Tool                        */
/*											   */
/* Owner       : This tool is owned by Gauss Research Group at School of Computing,        */
/*               University of Utah, Salt Lake City, USA.                                  */
/*               Please send your queries to: gauss@cs.utah.edu                            */
/*               Researh Group Home Page: http://www.cs.utah.edu/formal_verification/      */
/* Version     : beta 									   */
/* Last Edited : 03/12/2013                                                                */
/* Copyright   : Refer to LICENSE document for details 					   */
/*******************************************************************************************/
#include <string>
#include <assert.h>
#include <iostream>
#include <llvm/Pass.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/Function.h>
#include <llvm/Module.h>
#include <llvm/User.h>
#include <llvm/IRBuilder.h>
#include <llvm/Instructions.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/ADT/Statistic.h>
#include <llvm/CodeGen/MachineOperand.h>
#include <llvm/Support/CommandLine.h>
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/PassManager.h"
#include "llvm/CallingConv.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Assembly/PrintModulePass.h"

using namespace llvm;

Module* makeLLVMModule();

static cl::opt<int> f_prob("fp", cl::desc("User Defined Fault Probablity"), cl::value_desc("1-100"), cl::init(100), cl::ValueRequired);
static cl::opt<int> byte_val("b", cl::desc("Which byte to consider for fault injection"), cl::value_desc("0-3"), cl::init(0), cl::ValueRequired);
static cl::opt<bool> data_err("de", cl::desc("Inject Data Register Error"), cl::value_desc("0/1"), cl::init(1), cl::ValueRequired);
static cl::opt<int> ijo("ijo", cl::desc("Inject Error Only Once"), cl::value_desc("0/1"), cl::init(1), cl::ValueRequired);
static cl::opt<bool> ptr_err("pe", cl::desc("Inject Pointer Register Error"), cl::value_desc("0/1"), cl::init(0), cl::ValueRequired);

Value* func_corruptA;/*stores corrupt_Add() function*/
Value* func_corruptL;/*stores corruptL() function*/
Value* func_corrupt;/*stores corrupt() function*/
std::string cstr=""; /*stores fault site name used by fault injection pass*/
unsigned int lstsize=0; /*Stores instruction list used by static fault injection pass*/

/*Prints static fault injection statistics*/
void printStat(unsigned int indexloc, bool inst_flag, bool func_flag){
    if(!func_flag)
    {
       errs()<<"#################################################"<< '\n';
       errs()<<"Error: Couldn't select a valid function" << '\n';
       errs()<<"#################################################"<< '\n';
    }
    else{
       if(inst_flag){
      	 errs()<<"#################################################"<< '\n';
         errs()<<"Error injected in the function: "<< cstr <<'\n';
         errs()<<"Error injected in the instruction at position " << indexloc <<'\n' ;
         errs()<<"Number of instruction in the function: " << lstsize <<'\n' ;
         errs()<<"Successfully inserted fault!!" << '\n';            
         errs()<<"#################################################"<< '\n';
       }
       else{
         errs()<<"#################################################"<< '\n';
         errs()<<"Error: Couldn't select a valid instruction" << '\n';
         errs()<<"#################################################"<< '\n';
       }
    }
}

/*Injects static fault(s) into data register*/
bool InjectError_DataReg(Instruction *I)
{
    /*generate random probablity and check it against user defined probablity*/
    srand(time(NULL));
    int p=(rand()%100)+1;
    if(p>f_prob)        
        return false;
    
    /*Locate the instruction I in the basic block BB*/
    BasicBlock *BB = I->getParent();   
    BasicBlock::iterator BI;
    for(BI=BB->begin();BI!=BB->end();BI++)    
        if (BI == *I)
	   break;   
    Value *inst = &(*I);   
    
    unsigned int bPos=(8*byte_val)+rand()%8;
    unsigned int opPos=rand()%2;
    int mask = ~(0x1<<bPos);                                                    

    /*Check if I is of type BinaryOperator and inject error if true*/
    if(BinaryOperator *binOp = dyn_cast<BinaryOperator>(inst))
    { 						    
       Value *tVal=ConstantInt::get(binOp->getOperand(opPos)->getType(),mask);
       BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, binOp->getOperand(opPos), inst->getName(), BI);
       BI->setOperand(opPos,N);	
       return true;
    }/*end if*/

    /*Check if I is of type CmpInst and inject error if true*/
    if(CmpInst *cmpOp = dyn_cast<CmpInst>(inst))
    {      
       User* tcmpOp = &*cmpOp;
       Value *tVal=ConstantInt::get(tcmpOp->getOperand(opPos)->getType(),mask);
       BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, tcmpOp->getOperand(opPos), inst->getName(), BI);
       BI->setOperand(opPos,N);	
       return true;
    }/*end if*/
    return false;
}/*InjectError_DataReg*/


/*Injects static fault(s) into pointer register*/
bool InjectError_PtrError(Instruction *I)
{
    /*generate random probablity and check it against user defined probablity*/
    srand(time(NULL));
    int p=(rand()%100)+1;
    if(p>f_prob)        
        return false;

    /*Locate the instruction I in the basic block BB*/
    BasicBlock *BB = I->getParent();   
    BasicBlock::iterator BI;
    for(BI=BB->begin();BI!=BB->end();BI++)    
        if (BI == *I)
	   break;
    Value *inst = &(*I);  

    unsigned int bPos=(8*byte_val)+rand()%8;
    int mask = ~(0x1<<bPos);                     

    /*Check if I is of type StoreInst and inject error if true*/
    if(StoreInst *stInst = dyn_cast<StoreInst>(inst))
    {	
      Value *tVal=ConstantInt::get(stInst->getPointerOperand()->getType(),mask);
      Value *top = &(*(stInst->getPointerOperand()));	
      BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, stInst->getPointerOperand(), top->getName(), BI);	     
      BI->setOperand(0, N);		       
      return true;
    }/*end if*/

    /*Check if I is of type LoadInst and inject error if true*/
    if(LoadInst *ldInst = dyn_cast<LoadInst>(inst))
    {	
      Value *tVal=ConstantInt::get(ldInst->getPointerOperand()->getType(),mask);
      Value *top = &(*(ldInst->getPointerOperand()));	
      BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, ldInst->getPointerOperand(), top->getName(), BI);	     
      BI->setOperand(0, N);		       
      return true;
    }/*end if*/

    /*Check if I is of type AllocaInst and inject error if true*/
    if(AllocaInst *allcInst = dyn_cast<AllocaInst>(inst))
    {	
      User *allcInstu = &*allcInst;
      Value *tVal=ConstantInt::get(allcInstu->getOperand(0)->getType(),mask);
      Value *top = &(*(allcInstu->getOperand(0)));	
      BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, allcInstu->getOperand(0), top->getName(), BI);	     
      BI->setOperand(0, N);		       
      return true;
    }/*end if*/

    /*Check if I is of type CallInst and inject error if true*/
    if(CallInst *callInst = dyn_cast<CallInst>(inst))
    {	
      Value *tVal=ConstantInt::get(callInst->getCalledValue()->getType(),mask);
      Value *top = &(*(callInst->getCalledValue()));	
      BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, callInst->getCalledValue(), top->getName(), BI);	     
      BI->setOperand(0, N);		       
      return true;
    }/*end if*/

    /*Check if I is of type ReturnInst and inject error if true*/
    if(ReturnInst *retInst = dyn_cast<ReturnInst>(inst))
    {	
      Value *tVal=ConstantInt::get(retInst->getReturnValue()->getType(),mask);
      Value *top = &(*(retInst->getReturnValue()));	
      BinaryOperator *N = BinaryOperator::Create(Instruction::And, tVal, retInst->getReturnValue(), top->getName(), BI);	     
      BI->setOperand(0, N);		       
      return true;
    }/*end if*/
    return false;
}/*end InjectError_PtrError*/



/*Injects dynamic fault(s) into data register*/
bool InjectError_DataReg_Dyn(Instruction *I, int fault_index)
{
    srand(time(NULL));  
    /*Locate the instruction I in the basic block BB*/  
    Value *inst = &(*I);
    BasicBlock *BB = I->getParent();   
    BasicBlock::iterator BI,BINext;
    for(BI=BB->begin();BI!=BB->end();BI++)    
        if (BI == *I)
	   break;  

    /*Build argument list before calling Corrupt function*/
    CallInst* CallI=NULL;
    std::vector<Value*> args;
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),fault_index));
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ijo));
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),f_prob));
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),byte_val));

    /*Choose a fault site in StoreInst and insert Corrupt function call*/
    if(StoreInst* stOp = dyn_cast<StoreInst>(inst)) 
    {
       User* tstOp = &*stOp;
       args.push_back(tstOp->getOperand(0));
       if(tstOp->getOperand(0)->getType()->isIntegerTy(32)){
          CallI = CallInst::Create(func_corrupt,args,"call_corrupt",I);
       }
       else if(tstOp->getOperand(0)->getType()->isIntegerTy(64)){
          CallI = CallInst::Create(func_corruptL,args,"call_corruptL",I);
       }
       Value* corruptVal = &(*CallI);
       BI->setOperand(0,corruptVal);
       return true;
    }/*end if*/

    /*Choose a fault site in CmpInst and insert Corrupt function call*/
    if(CmpInst* cmpOp = dyn_cast<CmpInst>(inst))
    {
       unsigned int opPos=rand()%2;
       User* tcmpOp = &*cmpOp;
       args.push_back(tcmpOp->getOperand(opPos));
       if(tcmpOp->getOperand(opPos)->getType()->isIntegerTy(32)){          
          CallI = CallInst::Create(func_corrupt,args,"call_corrupt",I);
       }
       else if(tcmpOp->getOperand(opPos)->getType()->isIntegerTy(64)){
          CallI = CallInst::Create(func_corruptL,args,"call_corruptL",I);
       }
       Value* corruptVal = &(*CallI);
       BI->setOperand(opPos,corruptVal);
       return true;
    }/*end if*/

    /*Choose a fault site in a chosen instruction which neither CmpInst nor StoreInst 
      and insert Corrupt function call*/
    if(!isa<CmpInst>(inst) && !isa<StoreInst>(inst)) 
    {
       Instruction* INext=NULL;
       Instruction *IClone = I->clone();
       assert(IClone);
       IClone->insertAfter(I);
       Value *instC = &(*IClone);          
       BI = *IClone;
       args.push_back(instC);       
       /*Corrupt Variable*/      
       if(BI == BB->end()){
          if(inst->getType()->isIntegerTy(32)){
             CallI = CallInst::Create(func_corrupt,args,"call_corrupt",BB);
          }
          else if(inst->getType()->isIntegerTy(64)){
             CallI = CallInst::Create(func_corruptL,args,"call_corruptL",BB);
          }
          assert(CallI);
          CallI->setCallingConv(CallingConv::C);
       }
       else{
          BINext = BI;
          BINext++;
          INext = &*BINext;
          assert(INext);
          if(inst->getType()->isIntegerTy(32)){
             CallI = CallInst::Create(func_corrupt,args,"call_corrupt",INext);
          }
          else if(inst->getType()->isIntegerTy(64)){
             CallI = CallInst::Create(func_corruptL,args,"call_corruptL",INext);
          }
          assert(CallI);
          CallI->setCallingConv(CallingConv::C);
       }
       Value* corruptVal = &(*CallI);     
       inst->replaceAllUsesWith(corruptVal);
       return true;
    }/*end if*/
    return false;
}/*InjectError_DataReg_Dyn*/


/*Injects dynamic fault(s) into pointer register*/
bool InjectError_PtrError_Dyn(Instruction *I, int fault_index)
{
    /*Build argument list before calling Corrupt function*/
    srand(time(NULL));    
    std::vector<Value*> args;
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),fault_index));
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ijo));
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),f_prob));
    args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),byte_val));

    /*Locate the instruction I in the basic block BB*/  
    Value *inst = &(*I);  
    BasicBlock *BB = I->getParent();   
    BasicBlock::iterator BI;
    for(BI=BB->begin();BI!=BB->end();BI++)    
        if (BI == *I)
	   break;

    /*Choose the pointer operand in StoreInst and insert Corrupt function call*/
    if(StoreInst* stOp = dyn_cast<StoreInst>(inst)) 
    {
       /*Corrupt Variable*/
       args.push_back(stOp->getPointerOperand());
       CallInst* CallI = CallInst::Create(func_corruptA,args,"call_corrupt_add",I);
       Value* corruptVal = &(*CallI);
       BI->setOperand(1,corruptVal);
       return true;
    }/*end if*/

    /*Choose the pointer operand in LoadInst and insert Corrupt function call*/
    if(LoadInst *ldInst = dyn_cast<LoadInst>(inst))
    {	
       args.push_back(ldInst->getPointerOperand());
       CallInst* CallI = CallInst::Create(func_corruptA,args,"call_corrupt_add",I);
       Value* corruptVal = &(*CallI);
       BI->setOperand(0,corruptVal);
       return true;
    }/*end if*/

    /*Choose the pointer operand in AllocaInst and insert Corrupt function call*/
    if(AllocaInst *allcInst = dyn_cast<AllocaInst>(inst))
    {	
       User *allcInstu = &*allcInst;
       args.push_back(allcInstu->getOperand(0));
       CallInst* CallI = CallInst::Create(func_corruptA,args,"call_corrupt_add",I);
       Value* corruptVal = &(*CallI);
       BI->setOperand(0, corruptVal);		       
       return true;
    }/*end if*/

    /*Choose the pointer operand in CallInst and insert Corrupt function call*/
    if(CallInst *callInst = dyn_cast<CallInst>(inst))
    {	
       args.push_back(callInst->getCalledValue());
       CallInst* CallI = CallInst::Create(func_corruptA,args,"call_corrupt_add",I);
       Value* corruptVal = &(*CallI);
       BI->setOperand(0, corruptVal);		       
       return true;
  
    }/*end if*/
    return false;
}/*end InjectError_PtrError*/


/******************************************************************************************************************************/

/*Dynamic Fault Injection LLVM Pass*/
namespace {
  class dynfault : public ModulePass 
  {
    public:
	    static char ID; 
	    dynfault() : ModulePass(ID) {}	    
	    virtual bool runOnModule(Module &M)
            {	
                /*Check for assertion violation(s)*/
                assert(byte_val<=7 && byte_val>=0);
                assert(f_prob<=100 && f_prob>0);
                assert(ijo==1 || ijo==0);
                assert(ptr_err==1 || ptr_err==0);
                assert(data_err==1 || data_err==0);

                bool func_flag=false;
                bool insert_flag=false;
                StringRef lstr;
                srand(time(NULL));
  	        Module::FunctionListType &functionList = M.getFunctionList();
                
                /*Cache function references to be considered for fault injection*/
                unsigned int j=0;
	        for (Module::iterator it = functionList.begin(); it != functionList.end(); ++it,j++) 
                {
                     lstr = it->getName();
                     cstr = lstr.str();                                        
                     if(!cstr.compare("corrupt")){
                        func_corrupt =&*it;                                          
                     }
                     if(!cstr.compare("corruptL")){
                        func_corruptL =&*it;                        
                     }                     
                     if(!cstr.compare("corrupt_Add")){
                        func_corruptA =&*it;                        
                     }                     
                     if(!cstr.compare("main") || !cstr.compare("corrupt") || !cstr.compare("corruptL") || !cstr.compare("corrupt_Add")){
                         continue;                         
                     }
                     Function *F = it;	
		     if(F->begin() == F->end())
	                continue;	

                     /*Cache instruction references with in a function to be considered for fault injection*/             
		     func_flag=true;
 		     std::set<Instruction*> ilist;
                     for(inst_iterator I=inst_begin(F),E=inst_end(F);I!=E;I++){
                        Value *in = &(*I);  
                        if(data_err)
                           if(isa<BinaryOperator>(in) || 
                              isa<CmpInst>(in)        ||
                              isa<StoreInst>(in)      ||
                              isa<LoadInst>(in))
                           {                     
		              ilist.insert(&*I);                              
                           }
                        if(ptr_err)
                           if(isa<StoreInst>(in) || 
                              isa<LoadInst>(in)  ||
                              isa<CallInst>(in)  ||
                              isa<AllocaInst>(in)
                             )
                           {                     
		              ilist.insert(&*I);
                           }
                     }
                     /*Check if instruction list is empty*/
                     if(ilist.empty()){
                        errs() << "No Valid Instruction Found!!" << '\n';
                        return false;
                     }
                     lstsize = ilist.size();
                     unsigned int i=0;
                     /*Choose a random instuction from instruction list and insert either data or pointer error or both*/
                     for(std::set<Instruction*>::iterator its =ilist.begin();its!=ilist.end();its++,i++)                
                     {                          
 	                Instruction* inst = *its;
			if(data_err){
 	                   if(InjectError_DataReg_Dyn(inst,i))
                               insert_flag=true;                              
                        }
			if(ptr_err)
	                   if(InjectError_PtrError_Dyn(inst,i))
                               insert_flag=true;                                                                               

                     }/*end for*/
		}/*end for*/
		return false;
	    }/*end function definition*/
  };/*end class definition*/
}/*end namespace*/
char dynfault::ID = 0;
static RegisterPass<dynfault> F0("dynfault", "Dynamic Fault Injection emulating transient hardware error behavior");

/******************************************************************************************************************************/

/******************************************************************************************************************************/

/*Static Fault Injection LLVM Pass*/
namespace {
  class staticfault : public ModulePass 
  {
    public:
	    static char ID; 
	    staticfault() : ModulePass(ID) {}	    
	    virtual bool runOnModule(Module &M)
            {	
                /*Check for assertion violation(s)*/
                assert(byte_val<=7 && byte_val>=0);
                assert(f_prob<=100 && f_prob>0);
                assert(ijo==1 || ijo==0);
                assert(ptr_err==1 || ptr_err==0);
                assert(data_err==1 || data_err==0);
                bool func_flag=false;
                bool insert_flag=false;
                StringRef lstr;                
                srand(time(NULL));
  	        Module::FunctionListType &functionList = M.getFunctionList();
                unsigned int j=0;
                /*Cache function references to be considered for fault injection*/
	        for (Module::iterator it = functionList.begin(); it != functionList.end(); ++it,j++) 
                {
                     lstr = it->getName();
                     cstr = lstr.str();                   
                     if(!cstr.compare("main"))
                         continue;
                     Function *F = it;	
		     if(F->begin() == F->end())
	                continue;	
             
		     func_flag=true;
 		     std::set<Instruction*> ilist;
                     /*Cache instruction references with in a function to be considered for fault injection*/             
                     for(inst_iterator I=inst_begin(F),E=inst_end(F);I!=E;I++){
                        Value *in = &(*I);  
                        if(data_err)
                           if(isa<BinaryOperator>(in) || 
                              isa<CmpInst>(in))
                           {                     
		              ilist.insert(&*I);
                           }
                        if(ptr_err)
                           if(isa<StoreInst>(in) || 
                              isa<LoadInst>(in)  ||
                              isa<CallInst>(in)  ||
                              isa<AllocaInst>(in)
                             )
                           {                     
		              ilist.insert(&*I);
                           }
                     }
                     /*Check if instruction list is empty*/
                     if(ilist.empty()){
                        errs() << "No Valid Instruction Found!!" << '\n';
                        return false;
                     }
                     lstsize = ilist.size();
                     unsigned int r = rand()%ilist.size();
                     unsigned int i=0;
                     /*Choose a random instuction from instruction list and insert either data or pointer error or both*/
                     for(std::set<Instruction*>::iterator its =ilist.begin();its!=ilist.end();its++,i++)                
                     {
                          if(r==i){
 	                    Instruction* inst = *its;
			    if(data_err && !inst->mayReadOrWriteMemory())
 	                        if(InjectError_DataReg(inst))
                                   insert_flag=true;                             
                            
			    if(ptr_err && inst->mayReadOrWriteMemory())
	                        if(InjectError_PtrError(inst))
                                   insert_flag=true;                              
                                                        
                            if(insert_flag){
                               printStat(r,insert_flag,func_flag);
	                       return true;
                            }
			  }
                     }/*end for*/
		}/*end for*/
		return false;
	    }/*end function definition*/
  };/*end class definition*/
}/*end namespace*/
char staticfault::ID = 0;
static RegisterPass<staticfault> F1("staticfault", "Static Fault Injection emulating permanent hardware error behavior");

/******************************************************************************************************************************/


