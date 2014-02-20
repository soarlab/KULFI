/*******************************************************************************************/
/* Name        : Kontrollable Utah LLVM Fault Injector (KULFI) Tool                        */
/*											   										       */
/* Owner       : This tool is owned by Gauss Research Group at School of Computing,        */
/*               University of Utah, Salt Lake City, USA.                                  */
/*               Please send your queries to: gauss@cs.utah.edu                            */
/*               Researh Group Home Page: http://www.cs.utah.edu/formal_verification/      */
/* Version     : beta 									   								   */
/* Last Edited : 06/26/2013                                                                */
/* Copyright   : Refer to LICENSE document for details 					                   */
/*******************************************************************************************/

#include <sstream>
#include <fstream>
#include <map>
#include <vector>
#include <algorithm>
#include <iterator>
#include <string>
#include <assert.h>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <llvm/Pass.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/Argument.h>
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

// Enable this macro to use old code
// Otherwise, use the code on 2013-07-23
//#define IGNORE_20130723_CHANGES

using namespace llvm;
const char* getMyTypeName(const Value* v);
static IRBuilder<true, ConstantFolder, IRBuilderDefaultInserter<true> >* g_irbuilder;

static cl::opt<std::string> func_list("fn", cl::desc("Name(s) of the function(s) to be targeted"), cl::value_desc("func1 func2 func3"), cl::init(""), cl::ValueRequired);
static cl::opt<int> ef("ef", cl::desc("expected number of fault occurence"), cl::value_desc("Any value greater than or equal to 0 and less than or equal to tf"), cl::init(100), cl::ValueRequired);
static cl::opt<int> tf("tf", cl::desc("Total number of fault occurence"), cl::value_desc("Any value greater than 1 and less than or equal to tf"), cl::init(100), cl::ValueRequired);
static cl::opt<int> byte_val("b", cl::desc("Which byte to consider for fault injection"), cl::value_desc("0-7"), cl::init(-1), cl::ValueRequired);
static cl::opt<bool> data_err("de", cl::desc("Inject Data Register Error"), cl::value_desc("0/1"), cl::init(1), cl::ValueRequired);
static cl::opt<int> ijo("ijo", cl::desc("Inject Error Only Once"), cl::value_desc("0/1"), cl::init(1), cl::ValueRequired);
static cl::opt<int> print_fs("pfs", cl::desc("Print Fault Statistics"), cl::value_desc("0/1"), cl::init(0));
static cl::opt<bool> ptr_err("pe", cl::desc("Inject Pointer Register Error"), cl::value_desc("0/1"), cl::init(0), cl::ValueRequired);

// Injection "whitelist"
static std::list<std::string> inj_funcname_whitelist;
static bool shouldInjectFunction(const Function* f) {
	// If no whitelist entry ---> always "true"
	if(inj_funcname_whitelist.empty()) return true;
	else {
		std::string fn_name = f->getName().str();
		for(std::list<std::string>::iterator itr = inj_funcname_whitelist.begin();
			itr != inj_funcname_whitelist.end(); itr++) {
			if(!(fn_name.compare(*itr))) return true;
		}
	}
	return false;
}

static Instruction* getFirstNonPHINonLandingPad(BasicBlock* pBB) {
	Instruction* ret = pBB->getFirstNonPHI();
	BasicBlock::iterator itr;// = pBB->begin();
	for(itr = pBB->begin(); itr != pBB->end(); itr++) {
		if(isa<LandingPadInst>(*itr)) {
			itr++;
			ret = &*itr;
			return ret;
		}
	}
	return ret;
}

static void readFunctionInjWhitelist() {
	std::ifstream in("./funclist.txt");
	if(!(in.good())) {
		fprintf(stderr, "[dynfault] Function injection whitelist not enabled.\n");
		fprintf(stderr, "           Defaulting to injecting into all possible fault sites.\n");
		return;
	} else {
		std::string line;
		while(in.good()) {
			in >> line;
			fprintf(stderr, "[dynfault] %s\n", line.c_str());
			inj_funcname_whitelist.push_back(line);
		}
		in.close();
	}
	fprintf(stderr, "[dynfault] %lu entries in whitelist.\n",
		inj_funcname_whitelist.size());
}

Value* func_corruptIntData_8bit;
Value* func_corruptIntData_16bit;
Value* func_corruptIntData_32bit;
Value* func_corruptIntData_64bit;
Value* func_corruptFloatData_32bit;
Value* func_corruptFloatData_64bit;
Value* func_corruptFloatData_80bit; // X86 FP80
Value* func_corruptIntAdr_32bit;
Value* func_corruptIntAdr_64bit;
Value* func_corruptFloatAdr_32bit;
Value* func_corruptFloatAdr_64bit;
Value* func_print_faultStatistics;
Value* func_incrementFaultSitesEnumerated;
Value* func_printInstCount;
Value* func_initFaultInjectionCampaign;
Value* func_main;
Value* func_isNextFaultInThisBB;
std::string cstr=""; /*stores fault site name used by fault injection pass*/
unsigned int lstsize=0; /*Stores instruction list used by static fault injection pass*/

int g_fault_index = 0;
enum FaultType {
	DYN_FAULT_DATA,
	DYN_FAULT_PTR
};
// Instruction may change ?
static std::map<int, std::pair<std::string, FaultType> > g_fault_sites;

std::set<Instruction*> corrupted_ptrs;
std::map<BasicBlock*, unsigned> bb_fs_counts; // Fault Site count of each BB
std::map<BasicBlock*, std::string> bb_names; // BB names.

// Use-def graph
// The same pointer would always point to the [source] (uninjected) instruction
//   this would help us locate the instruction in the use-def chain
#ifdef TOMMY_TEST
std::map<const Value*, std::string> test0;
#endif
unsigned long num_nodes;
std::set<unsigned long> is_in_chain; // Is a node in the use-def chain?
std::set<unsigned long> is_terminator; // Is this a terminator instruction?
std::set<int> injected_fault_indices; // Is the fault site at this index really injected?
std::map<const BasicBlock*, std::list<unsigned long> > nodeids_in_basicblocks;
std::map<const Function*, std::list<const BasicBlock*> > bbs_in_funcs;
std::map<const Value*, unsigned long> fault_site_to_nodeid;
std::map<unsigned long, int> nodeid_to_fault_site_id;
std::map<unsigned long, const char*> node_type_names;
std::list<std::pair<unsigned long, unsigned long> > usedef_edge_list;
std::list<std::pair<unsigned long, unsigned long> > branch_edge_list;

// Predicate "shall we inject errors in THIS BB?"
//   Is a Boolean value.
std::map<const BasicBlock*, Value*> bb_to_pred;
// There should not be "incrementFaultSiteCount"s for
// "alternative BB" and "next BB"'s!
std::set<BasicBlock*> blacklisted_bbs;
void writeFaultSiteDOTGraph();

// Don't use this routine. It's painfully slow!
static void logFaultSiteInfo(const Instruction* inst, int fault_index, FaultType fault_type) {
	assert((g_fault_sites.find(fault_index) == g_fault_sites.end()) &&
		"Each fault site shall have a unique number.");
#ifdef TOMMY_TEST
	std::string inst_str = instToString(inst);
	if(!(test0[inst] == inst_str)) {
		errs() << test0[inst] << "   vs   " << inst_str << "\n";
	}
#else
	std::string inst_str = "blah";
#endif
	// Instruction to Instruction I.D.
	const Value* site = dynamic_cast<const Value*>(inst);
	assert(site);
	if(site) {
		unsigned long node_id = fault_site_to_nodeid.at(site);
		nodeid_to_fault_site_id[node_id] = fault_index;
	}
	g_fault_sites[fault_index] = std::make_pair(inst_str, fault_type);
}

// Do not perform fault injection to these functions!
static const char* blacklist[] = {
	"shouldInject",
	"incrementInstCount",
	"print_faultStatistics",
	"__printInstCount",
	"printFaultInfo",
	"initializeFaultInjectionCampaign",
	"incrementFaultSiteHit",
	"incrementInstCount",
	"__printInstCount",
	"corruptIntData_16bit",
	"corruptIntData_32bit",
	"corruptIntData_64bit",
	"corruptIntData_8bit",
	"corruptIntData_1bit",
	"corruptFloatData_32bit",
	"corruptFloatData_64bit",
	"corruptFloatData_80bit",
	"corruptIntAdr_32bit",
	"corruptIntAdr_64bit",
	"corruptFloatAdr_32bit",
	"corruptFloatAdr_64bit",
	"print_faultStatistics",
	"printFaultInfo",
	"main",
	"onCountDownReachesZero",
	"isNextFaultInThisBB",
	"incrementFaultSiteCount",
	"onEnteringBB",
	"_ZNK3MPI8Cartcomm5CloneEv",
	"flushBBEntries",
	"_ZN11BBHistEntryC1Ev", // BBHistEntry::BBHistEntry()
	"_ZN11BBHistEntryC2Ev",
	"_ZN11BBHistEntryC3Ev", // Can anyone tell me why {1,2,3}?
	"writeFaultSiteHitHistogram",
	"_GLOBAL__I_a", // .text.startup
	"MY_SET_SIGSEGV_HANDLER",
	"EnableKulfi",
	"DisableKulfi"
};

static bool isFunctionNameBlacklisted(const char* fn) {
	for(unsigned i=0; i<sizeof(blacklist) / sizeof(const char*); i++) {
		if(!strcmp(blacklist[i], fn)) return true;
	}
	return false;
}

// Counts how many fault sites there are in the BasicBlocks in this Module.
static void appendInstCountCalls(Module& M) {
	Module::FunctionListType &fl = M.getFunctionList();
	for(Module::iterator it = fl.begin(); it!=fl.end(); it++) {
		Function& F = *it;
		std::string cstr = it->getName().str();
		bool is_blacklisted = isFunctionNameBlacklisted(cstr.c_str());
		if(is_blacklisted) continue;
		for(Function::iterator bi = F.begin(); bi!=F.end(); bi++) {
			BasicBlock* bb = &(*bi);
			if(blacklisted_bbs.find(bb) != blacklisted_bbs.end()) continue;

			Instruction* first_inst = getFirstNonPHINonLandingPad(bb);
			
			unsigned size = 0;
			if(!(bb_fs_counts.find(bb) != bb_fs_counts.end())) {
				bb->getParent()->dump();
				assert(false);
			}
			size = bb_fs_counts[bb];
			if(size < 1) continue;
			std::vector<Value*> args;
			assert(bb_names.find(bb) != bb_names.end());
			std::string bbn = bb_names[bb];
			
			// Create a global variable.
			IRBuilder<> irb(bb);
			Value* global_str_ptr = irb.CreateGlobalString(bbn, "bbname");
			std::vector<Value*> indices;
			indices.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()), 0));
			indices.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()), 0));
			
			GetElementPtrInst* gep_str = GetElementPtrInst::CreateInBounds(global_str_ptr,
				indices,
				"bbname", first_inst);
			
			args.push_back(gep_str);
			args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),
				size));
			CallInst* inc_call = CallInst::Create(func_incrementFaultSitesEnumerated, args,
				"", first_inst);
			
			assert(inc_call);
			// Do not inject into this call
			corrupted_ptrs.insert(inc_call);
		}

		if(cstr == "main") { // Outro
			BasicBlock* bb = &(it->back());
			Instruction* first_inst = bb->getFirstNonPHI();
			CallInst* instcnt_call = CallInst::Create(func_printInstCount, 
				std::vector<Value*>(), "", first_inst);
			assert(instcnt_call);
		}
	}
}

// Description of this function:
// It corrupts a pointer (means: inst->getType()->isPointerType() == true)
// by converting it to a 64-bit integer (b/c assuming a 64-bit machine),
//    corrupting the integer with existing routines, and converting it back.
// One caveat is that "replace all uses" of inst should be replaced with
//    "replace all uses but the first" when updating uses of inst.
Value* CorruptPointer(Value* inst,
	BasicBlock::iterator BINext, // 2 cases: may be the end of BB or in a BB.
	BasicBlock* BB,
	std::vector<Value*>& _args) {
	Instruction* INext = &*BINext;
	char name_ptr2int[40], corr_name_ptr2int[40], corr_name_ptr[40];
	sprintf(name_ptr2int, "TheFirstGuy");
	sprintf(corr_name_ptr2int, "TheSecondGuy");
	sprintf(corr_name_ptr, "TheThirdGuy");
	CallInst* CallI = NULL;
	assert(inst->getType()->isPointerTy());
	Value* iPtr = NULL; // Pointer converted to Integer.
	if(INext!=NULL) {
		iPtr = new PtrToIntInst(inst,
			IntegerType::getInt64Ty(getGlobalContext()),
			name_ptr2int,
			INext
		);
		corrupted_ptrs.insert((Instruction*)(iPtr));
	} else {
		iPtr = new PtrToIntInst(inst,
			IntegerType::getInt64Ty(getGlobalContext()),
			name_ptr2int,
			BB
		);
		corrupted_ptrs.insert((Instruction*)(iPtr));
	}
	if(!iPtr) assert(0);
	std::vector<Value*> args;// = _args;
	args.clear();
	// Increment g_fault_index
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),g_fault_index));
	std::vector<Value*>::iterator itr;
	itr = _args.begin();
	itr++;
	for(; itr!=_args.end(); itr++) {
		Value* v = *itr;
		args.push_back((Value*)v);
	}
	args.push_back(iPtr); // <--- The input param is not modified!

	
	#define CHECK_ARGS(fn) \
	{ \
		Function* f = (Function*)(fn); \
		errs() << "::::" << f->getArgumentList().size() << "," << args.size() ; \
		errs() << "\n"; \
		inst->getType()->dump(); \
		errs() << "\n"; \
		Function::ArgumentListType::iterator itr = f->getArgumentList().begin(); \
		std::vector<Value*>::iterator itr2 = args.begin(); \
		for(; itr!=f->getArgumentList().end(); itr++, itr2++) { \
			Value* v = *itr2; \
			Argument* a = &(*itr); \
			Type* t_v = v->getType(); \
			Type* t_a = a->getType(); \
			errs() << " :: "; \
			t_v->dump();  \
			errs() << " ";  \
			t_a->dump();  \
			errs() << " \n"; \
		} \
	}
//	CHECK_ARGS(func_corruptIntAdr_64bit);	
	
	Value* corruptedPtr = NULL;
	if(INext != NULL) { 
		CallI = CallInst::Create(func_corruptIntData_64bit, args, corr_name_ptr2int, INext);
		corruptedPtr = new IntToPtrInst(CallI,
			inst->getType(),
			corr_name_ptr,
			INext
		);
		corrupted_ptrs.insert(CallI);
		corrupted_ptrs.insert((Instruction*)(corruptedPtr));
	} else {
		CallI = CallInst::Create(func_corruptIntData_64bit, args, corr_name_ptr2int, BB);
		corruptedPtr = new IntToPtrInst(CallI,
			inst->getType(),
			corr_name_ptr,
			BB
		);
		corrupted_ptrs.insert(CallI); 
		corrupted_ptrs.insert((Instruction*)(corruptedPtr));
	}
	return corruptedPtr;
}

#ifndef IGNORE_20130723_CHANGES
static PHINode* createBranchForCorruptInst(Value* corrupted,
	Value* original) {

	PHINode* corruptValPhi = NULL;
	BasicBlock *injBB, *prevBB, *nextBB;

	prevBB = ((Instruction*)corrupted)->getParent();
	BasicBlock::iterator split_at_inj, split_at_next, itr;
	for(itr = prevBB->begin(); itr != prevBB->end(); itr++) {
		if((&*itr) == corrupted) {
			split_at_inj = itr;
			break;
		}
	}
	itr++;
	split_at_next = itr;

	// Using a predicate instead of calling corrupt* function
	//    at every fault site.

	// BEFORE:
	// [  BB             (Corrupt)                  ]
	// AFTER:
	// [  prevBB  ] [ injBB  (Corrupt) ] [  nextBB  ]
	assert(itr != prevBB->end());
	injBB  = prevBB->splitBasicBlock(split_at_inj);
	nextBB = injBB ->splitBasicBlock(split_at_next);
	blacklisted_bbs.insert(injBB);
	blacklisted_bbs.insert(nextBB);
	TerminatorInst* prevBBT_old = prevBB->getTerminator();
	prevBBT_old->eraseFromParent();
	Value* pred = (Value*)(bb_to_pred.at(prevBB));
	BranchInst::Create(injBB, nextBB, pred, prevBB);
	bb_to_pred[nextBB] = pred;

	corruptValPhi = PHINode::Create(original->getType(), 0, "Corrupted",
		&(nextBB->front()));
	corruptValPhi->addIncoming(original, prevBB);
	corruptValPhi->addIncoming(corrupted, injBB);

	return corruptValPhi;
}

// This is the major change on 20130723
//   I hope this would make the resultant binaries run faster
// This all happens inside 1 BB, so it should be safe to replace
//   the uses of "original" only in the current BB
static void wrapCorruptInstWithBranch(Value* corrupted, 
	Value* original) {
	PHINode* corruptValPhi = createBranchForCorruptInst(corrupted, original);
	// replace uses of "original" with "corrupted"
	assert(corruptValPhi);
	BasicBlock* nextBB = corruptValPhi->getParent();
	BasicBlock::iterator bi = nextBB->begin();
	bi++; // Skip the PHINode
	while(bi != nextBB->end()) {
		Instruction* valu = &(*bi);
		valu->replaceUsesOfWith(original, corruptValPhi);
		bi++;
	}
	return;
}

// Fault Site count down is messed by CallInsts.
// For a given piece of code that looks like this:
// [ Inst ] [ Inst ] [ Inst ] [ Call ] [ Inst ]
// What I want to do is decrement countdown by 5 @ entry into BB
// But I can't do this since Call changes control flow and we overcount
//
// So the solution is ... split the BB into 3 BB's
// The BBs before & after the CallInst decrement the countdown by
//   their respective #s of fault sites.
//
// [ Inst ] [ Inst ] [ Inst ]          [ Call ]         [ Inst ]
//
static BasicBlock::iterator getFirstCallInst(BasicBlock* bb) {
	BasicBlock::iterator it;
	for(it = bb->begin(); it!=bb->end(); it++) {
		Instruction* inst = &(*it);
		if(isa<CallInst>(inst)) {
			return it;
		}
	}
	return bb->end();
}
static void splitBBOnCallInsts(Module& M) {
	Module::FunctionListType &fnList = M.getFunctionList();
	for(Module::iterator it = fnList.begin(); it != fnList.end(); it++) {
		Function& F = *it;
		Function::iterator startFrom = F.begin();
		while(true) {
			bool is_found = false; // found CallInst in function
			Function::iterator currBB = F.begin();
			BasicBlock::iterator itr_callI;
			// while currBB has a CallInst

			// move to "next-BB"
			while(currBB != startFrom && currBB != F.end()) {
				currBB++;
			}
			if(currBB == F.end()) break;
			assert(currBB == startFrom);

			do {
				for(; currBB != F.end(); currBB++) {
					BasicBlock* bb = &(*currBB);
					itr_callI = getFirstCallInst(bb);
					if(itr_callI != bb->end()) {
						is_found = true;
						break;
					}
				}
			} while(false);

			if(is_found) {
				BasicBlock* callBB = (*currBB).splitBasicBlock(itr_callI, "callBB");
				blacklisted_bbs.insert(callBB);
				BasicBlock::iterator next2 = callBB->begin();
				next2++;
				BasicBlock* nextStart = callBB->splitBasicBlock(next2, "nextCallBB");
				bool is_ok = false;
				for(Function::iterator itr = F.begin(); itr!=F.end(); itr++) {
					if((&(*itr)) == nextStart) {
						startFrom = itr;
						is_ok = true;
					}
				}
				assert(is_ok);
			} else break;
		}
	}
}
#endif
void addBBEntryCalls(Module& M) {
	const unsigned LEN = 1024;
	char tmp[LEN]; // Function name may be very long, resulting in stack smashing
	unsigned len = 0;
	std::set<std::string> used_names;
	Module::FunctionListType &fnList = M.getFunctionList();
	for(Module::iterator it = fnList.begin(); it != fnList.end(); it++) {
		Function& F = *it;
		Function::iterator it2 = F.begin();
		unsigned fnbbcnt = 0; // fnbbcnt reads "function BB count".
		for(; it2 != F.end(); it2++) {
			BasicBlock* pBB = &(*it2);
			std::string bbname, bbname1;
			if(pBB->getName().size() > 0) {
				bbname = pBB->getName();
			} else {
				len = strlen(F.getName().data());
				assert(len <= LEN); 
				sprintf(tmp, "%s_%u", F.getName().data(), fnbbcnt);
				bbname = tmp;
			}
			unsigned retry_cnt = 0;
			bbname1 = bbname;
			while(used_names.find(bbname) != used_names.end()) {
				retry_cnt++;
				len = strlen(bbname1.c_str());
				assert(len <= LEN);
				sprintf(tmp, "%s_%u", bbname1.c_str(), retry_cnt);
				bbname = tmp;
			}
			used_names.insert(bbname);
			bb_names[pBB] = bbname;
			fnbbcnt++;
		}
	}
}

std::vector<std::string> splitAtSpace(std::string spltStr){
	std::vector<std::string> strLst;
	std::istringstream isstr(spltStr);
	copy(std::istream_iterator<std::string>(isstr), 
		std::istream_iterator<std::string>(), 
		std::back_inserter<std::vector<std::string> >(strLst));
	return strLst;
}

/*Injects dynamic fault(s) into data register*/
bool InjectError_DataReg_Dyn(Instruction *I, int fault_index)
{
	if(I == NULL) return false;

	// Log Fault Site information
	logFaultSiteInfo(I, fault_index, DYN_FAULT_DATA);

	/*Locate the instruction I in the basic block BB*/  
	Value *inst = &(*I);    
	if(corrupted_ptrs.find(I) != corrupted_ptrs.end()) return false;
	
	BasicBlock *BB = I->getParent();   
	BasicBlock::iterator BI, BINext;
	for(BI=BB->begin(); BI!=BB->end(); BI++) { if(BI == *I) break; }

	/*Build argument list before calling Corrupt function*/
	CallInst* CallI=NULL;
	std::vector<Value*> args;
	args.clear();
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),fault_index));
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ijo));
	if(print_fs)
		 args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),0));
	else
		 args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ef));
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),tf));
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),byte_val));

	/*Choose a fault site in StoreInst and insert Corrupt function call*/
	if(StoreInst* stOp = dyn_cast<StoreInst>(inst)) 
	{
		User* tstOp = &*stOp;
		args.push_back(tstOp->getOperand(0));
		CallI = NULL;
		/*Integer Data*/
		if(tstOp->getOperand(0)->getType()->isIntegerTy(16)){
			CallI = CallInst::Create(func_corruptIntData_16bit,args,"call_corruptIntData_16bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} else if(tstOp->getOperand(0)->getType()->isIntegerTy(32)){
			CallI = CallInst::Create(func_corruptIntData_32bit,args,"call_corruptIntData_32bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} else if(tstOp->getOperand(0)->getType()->isIntegerTy(64)){
			CallI = CallInst::Create(func_corruptIntData_64bit,args,"call_corruptIntData_64bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} else if(tstOp->getOperand(0)->getType()->isIntegerTy(8)) {
			CallI = CallInst::Create(func_corruptIntData_8bit,args,"call_corruptIntData_8bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} /*Float Data*/
		else if(tstOp->getOperand(0)->getType()->isFloatTy()){
			CallI = CallInst::Create(func_corruptFloatData_32bit,args,"call_corruptFloatData_32bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} else if(tstOp->getOperand(0)->getType()->isDoubleTy()){
			CallI = CallInst::Create(func_corruptFloatData_64bit,args,"call_corruptFloatData_64bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		}

		if(CallI) {
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			// BI is invalidated after splitting BBs, so we shouldn't use BI
			I->setOperand(0, corruptValPhi);
#endif
			return true;
		} else {
			Value* inst = tstOp->getOperand(0);
			if(inst->getType()->isPointerTy()) {
				if(ptr_err == 1) {
					// When data_err and ptr_err are enabled simultaneously,
					//    and if the operand 0 is of pointer type, it should
					//    have already been corrupted.
//					inst->dump();
//					errs() << corrupted_ptrs.size() << " etys\n";
					if(corrupted_ptrs.find(I) != corrupted_ptrs.end()) return false;
//					errs() << "args has " << args.size() << "etys\n";
					args.pop_back();
					Value* corruptedPtr = CorruptPointer(inst, I, BB, args);
//					errs() << "old store: "; tstOp->dump();
					tstOp->replaceUsesOfWith(inst, corruptedPtr);
//					errs() << "inst: "; inst->dump();
//					errs() << "corrupted: "; corruptedPtr->dump();
//					errs() << "new store: "; tstOp->dump();
				}
			}
//			errs() << "[DataReg_Dyn Store Inst not captured] ";
//			errs() << *(tstOp);
//			errs() << "\n";
			return false;
		}
		tstOp->dump();
		assert(0);
	}/*end if*/

	/*Choose a fault site in CmpInst and insert Corrupt function call*/
	if(CmpInst* cmpOp = dyn_cast<CmpInst>(inst))
	{
		unsigned int opPos=rand()%2;
		User* tcmpOp = &*cmpOp;
		args.push_back(tcmpOp->getOperand(opPos));
		CallI = NULL;
		
		// To make the code more succinct!
		#define STR(x) #x
		#define FuncCorrupt(nbits) func_corruptIntData_ ## nbits ## bit
		#define VarCorrupt(nbits) call_corruptIntData_ ## nbits ## bit
		#define InjectInt(nbits) \
			CallI = CallInst::Create(FuncCorrupt(nbits), args, STR(Corrupt(nbits)), I); \
			assert(CallI); \
			CallI->setCallingConv(CallingConv::C);
		
		if(tcmpOp->getOperand(opPos)->getType()->isIntegerTy(16)){          
			InjectInt(16);
		} else if(tcmpOp->getOperand(opPos)->getType()->isIntegerTy(32)){          
			InjectInt(32);
		} else if(tcmpOp->getOperand(opPos)->getType()->isIntegerTy(64)){
			InjectInt(64);
		} else if(tcmpOp->getOperand(opPos)->getType()->isIntegerTy(1)) {
			// The following code has not been tested
			// "Boolean" types should be handled differently b/c there is no "bool" in C
			assert(!(BI == BB->end())); // the last instr. in a BB shall not be a BOOL value.
			BINext = BI; BINext++;
			Instruction* INext = &(*BINext);
			CastInst* cast8 = CastInst::CreateZExtOrBitCast(I, IntegerType::getInt8Ty(getGlobalContext()), "boolToChar", INext);
			CallI = CallInst::Create(func_corruptIntData_8bit, args, "call_corruptIntData_8bits", cast8);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			CastInst* cast1 = CastInst::CreateTruncOrBitCast(CallI, IntegerType::getInt1Ty(getGlobalContext()), "charToBool", INext);
			
			BI->setOperand(opPos, cast1);
			return true;
		} else { // OKay, it's a pointer....
			// Convert to 64-bit integer, corrupt it, then convert back
			
#ifndef IGNORE_20130723_CHANGES
			BINext = BI; BINext++;
			// Also need split BB here.
			Type* the_op_type = tcmpOp->getOperand(opPos)->getType();
			if(the_op_type->isPointerTy()) {
				PHINode* corruptValPhi = NULL;
				BasicBlock *injBB, *prevBB, *nextBB;
				prevBB = cmpOp->getParent();

				// prevBB
				BasicBlock::iterator split_at_inj, split_at_next, itr;
				for(itr = prevBB->begin(); itr!=prevBB->end(); itr++)
					if((&*itr) == cmpOp) break;
				split_at_inj = itr;
				assert(split_at_inj  != prevBB->end());
				injBB = prevBB->splitBasicBlock(split_at_inj);

				Instruction* inj_insert_here = &(injBB->front());

				// injBB
				Value* i_addr = new PtrToIntInst(
					tcmpOp->getOperand(opPos),
					IntegerType::getInt64Ty(getGlobalContext()),
						tcmpOp->getOperand(opPos)->getName(),
					//I 
					inj_insert_here
				);
				if(!i_addr) { assert(0 && "Cannot PtrToInt inst. This should not happen!"); }
				args.pop_back();
				args.push_back(i_addr);
				CallI = CallInst::Create(func_corruptIntData_64bit,
					args,
					tcmpOp->getOperand(opPos)->getName(),
					//I
					inj_insert_here
				);
				Value* corrupted_ptr = new IntToPtrInst(
					CallI,
					the_op_type,
					tcmpOp->getOperand(opPos)->getName(),
					//I
					inj_insert_here
				);

				// nextBB
				split_at_next = injBB->begin();
				while(true) {
					if((&*split_at_next) == inj_insert_here) break;
					split_at_next++;
				}
				nextBB = injBB->splitBasicBlock(split_at_next);
				corruptValPhi = PHINode::Create(the_op_type, 0, "BBBB",
					&(nextBB->front()));
				corruptValPhi->addIncoming(tcmpOp->getOperand(opPos), prevBB);
				corruptValPhi->addIncoming(corrupted_ptr, injBB);

				// prevBB's terminator (do this after {next|inj}BB are ready.)
				TerminatorInst* prevBBT_old = prevBB->getTerminator();
				prevBBT_old->eraseFromParent();
				Value* pred = (Value*)(bb_to_pred.at(prevBB));
				BranchInst::Create(injBB, nextBB, pred, prevBB);
				bb_to_pred[nextBB] = pred;
				blacklisted_bbs.insert(injBB);
				blacklisted_bbs.insert(nextBB);

				// Blacklist them (do not corrupt them once more in ptr corruption)
				corrupted_ptrs.insert(CallI);
				corrupted_ptrs.insert((Instruction*)(tcmpOp->getOperand(opPos)));
				corrupted_ptrs.insert((Instruction*)(corrupted_ptr));
				corrupted_ptrs.insert(corruptValPhi);

				cmpOp->setOperand(opPos, corruptValPhi);
				return true;
			}
#else
			BINext = BI; BINext++;
			Type* the_op_type = tcmpOp->getOperand(opPos)->getType();
			if(the_op_type->isPointerTy()) {
				Value* i_addr = new PtrToIntInst(
					tcmpOp->getOperand(opPos),
					IntegerType::getInt64Ty(getGlobalContext()),
					    tcmpOp->getOperand(opPos)->getName(),
					I
				);
				if(!i_addr) { assert(0 && "Cannot PtrToInt inst. This shall not happen!"); }
				args.pop_back();
				args.push_back(i_addr);
				CallI = CallInst::Create(func_corruptIntData_64bit,
					args,
					tcmpOp->getOperand(opPos)->getName(),
					I
				);
				Value* corrupted_ptr = new IntToPtrInst(
					CallI,
					the_op_type,
					tcmpOp->getOperand(opPos)->getName(),
					I
				);
				// Blacklist them (do not corrupt them once more in ptr corruption)
				corrupted_ptrs.insert(CallI);
				corrupted_ptrs.insert((Instruction*)(tcmpOp->getOperand(opPos)));
				corrupted_ptrs.insert((Instruction*)(corrupted_ptr));
				cmpOp->setOperand(opPos, corrupted_ptr);
				return true;
			}
#endif
		}
		
		
		/* Float Data */
		if(tcmpOp->getOperand(opPos)->getType()->isFloatTy()){
			CallI = CallInst::Create(func_corruptFloatData_32bit,args,"call_corruptFloatData_32bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} else if(tcmpOp->getOperand(opPos)->getType()->isDoubleTy()){
			CallI = CallInst::Create(func_corruptFloatData_64bit,args,"call_corruptFloatData_64bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		} else if(tcmpOp->getOperand(opPos)->getType()->isX86_FP80Ty()) {
			errs() << "[DataReg_Dyn] FP80\n";
			CallI = CallInst::Create(func_corruptFloatData_80bit,args,"call_corruptfloatData_80bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
		}
		
		if(CallI) {
#ifdef IGNORE_20130723_CHANGES
			Value* corruptVal = &(*CallI);
			BI->setOperand(opPos, corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(CallI,
				I->getOperand(opPos));
			// BI is invalidated
			I->setOperand(opPos, corruptValPhi);
#endif		
			return true;
		} else {
			errs() << "[DataReg_Dyn CmpInst not injected] "
				<< *(cmpOp->getType()) << "\n";
			cmpOp->dump();
			return false;
		}
		assert(0);
	}/*end if*/

	/*Choose a fault site in a chosen instruction which neither CmpInst nor StoreInst 
		and insert Corrupt function call*/
	if(!isa<CmpInst>(inst) && !isa<StoreInst>(inst)) 
	{
		/*
		Instruction* INext=NULL;
		Instruction *IClone = I->clone();
		assert(IClone);
		IClone->insertAfter(I); // Why clone ?
		Value *instC = &(*IClone);
		BI = *IClone;
		args.push_back(instC);
		*/
		BasicBlock::iterator BI2 = BI; BI2++;
		if(BI2 == BB->end()) {
			errs() << "Oh!\n";
			return false;
		}
		Instruction* INext = &(*BI2);
		Value* instC = &(*I);
		args.push_back(instC);
		
		
		
		/*Corrupt Variable*/      
		if(BI == BB->end()){
			/* void */
			if(inst->getType()->isVoidTy())
				return false;

			/*Integer Data*/
			if(inst->getType()->isIntegerTy(16)){
				CallI = CallInst::Create(func_corruptIntData_16bit,args,"call_corruptIntData_16bit",BB);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isIntegerTy(32)){
				
				
				CallI = CallInst::Create(func_corruptIntData_32bit,args,"call_corruptIntData_32bit",BB);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isIntegerTy(64)){
				CallI = CallInst::Create(func_corruptIntData_64bit,args,"call_corruptIntData_64bit",BB);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isIntegerTy(8)) {
				CallI = CallInst::Create(func_corruptIntData_64bit,args,"call_corruptIntData_8bit",BB);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C); 
			}

			/*Float Data*/
			if(inst->getType()->isFloatTy()){
				CallI = CallInst::Create(func_corruptFloatData_32bit,args,"call_corruptFloatData_32bit",BB);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isDoubleTy()){
				CallI = CallInst::Create(func_corruptFloatData_64bit,args,"call_corruptFloatData_64bit",BB);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			}

		} else {
			BINext = BI;
			BINext++;
			INext = &*BINext;
			assert(INext);
			/*Integer Data*/
			
			if(inst->getType()->isVoidTy()) return false;

			if(inst->getType()->isIntegerTy(16)){
				CallI = CallInst::Create(func_corruptIntData_16bit, args, "call_corruptIntData_16bit", INext);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isIntegerTy(32)){
				CallI = CallInst::Create(func_corruptIntData_32bit, args, "call_corruptIntData_32bit", INext);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isIntegerTy(64)){
				CallI = CallInst::Create(func_corruptIntData_64bit, args, "call_corruptIntData_64bit", INext);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isIntegerTy(8)){
				CallI = CallInst::Create(func_corruptIntData_8bit, args, "call_corruptIntData_8bit", INext);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} /*Float Data*/
			else if(inst->getType()->isFloatTy()){
				CallI = CallInst::Create(func_corruptFloatData_32bit, args, "call_corruptFloatData_32bit", INext);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			} else if(inst->getType()->isDoubleTy()){
				CallI = CallInst::Create(func_corruptFloatData_64bit, args, "call_corruptFloatData_64bit", INext);
				assert(CallI);
				CallI->setCallingConv(CallingConv::C);
			}
		}
		if(CallI) {
			Value* corruptVal = &(*CallI);

			// The first BI2++:  The inserted instruction, don't substitute 
			// The second BI2++: The one after the inserted instruction, substitute
			#define INJECTION_METHOD_ONE \
			BasicBlock::iterator BI2 = BI; \
			BI2++; \
			BI2++; \
			while(BI2 != BB->end()) { \
				Instruction* valu = &(*BI2); \
				valu->replaceUsesOfWith(inst, corruptVal); \
				BI2++; \
			}

#ifdef IGNORE_20130723_CHANGES
			INJECTION_METHOD_ONE;
#else
			// Fix on 20130725
			// After this change, use of inst may be across >1 BB's
			if(isa<CallInst>(inst)) {
				Function* F = BB->getParent();
				Function::iterator FI = F->begin();
				while(FI != F->end()) {
					if((&(*FI)) == BB) break;
					FI++; // FI should point to BI's BB
				}

				BasicBlock::iterator BI2 = BI;
				BI2++;
				BI2++;
				
				while(true) {
					while(BI2 != BB->end()) {
						Instruction* valu = &(*BI2);
						valu->replaceUsesOfWith(inst, corruptVal);
						BI2++;
					}
					FI++;
					if(FI == F->end()) break;
					BB = &(*FI);
					BI2 = BB->begin();
				}
			} else {
				wrapCorruptInstWithBranch(corruptVal, inst);
			}
#endif
			return true;
		} else {
			return false;
			/*
			if(inst->getType()->isPointerTy() && ptr_err==1) {
				if(corrupted_ptrs.find(I) != corrupted_ptrs.end()) return false;

				args.pop_back();
				// How about casting to a 64 bit, corrupt, and converting back?
				Value* corruptedPtr = CorruptPointer(inst, INext, BB, args);
				
				// -------------------------------------------------------------------
				// CAUTION! Only uses AFTER the first use can be replaced!!!!
				// -------------------------------------------------------------------
				//  (Converted code)
				//  %m1 = blah blah blah        Using replaceAllUsesWith will also overwrite
				//  %First = %m1 to INT   <---- this m1. This is not desired and results in a
				//  %Second = corrupt %First          broken module
				//  %Third = %Second to %m1's type
				//
				//inst->replaceAllUsesWith(corruptedPtr);
				{
					BasicBlock::iterator BI2 = BINext;
					while(BI2 != BB->end()) {
						Instruction* valu = &(*BI2);
						valu->replaceUsesOfWith(inst, corruptedPtr);
						BI2++;
					}
				}
				return true;
			} else {
				errs() << "[DataReg_Dyn Other Inst not recognized] " <<
					*(inst->getType()) << "\n";
				return false;
			}
			*/
		}
	}/*end if*/
	return false;
} /* InjectError_DataReg_Dyn */


/*Injects dynamic fault(s) into pointer register*/
bool InjectError_PtrError_Dyn(Instruction *I, int fault_index)
{	
	if(I==NULL) return false;
	CallInst* CallI=NULL;

	// Log fault site information
	logFaultSiteInfo(I, fault_index, DYN_FAULT_PTR);

	/*Build argument list before calling Corrupt function*/
	std::vector<Value*> args; args.clear();
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),fault_index));
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ijo));
	if(print_fs) args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),0));
	else args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ef));
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),tf));
	args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),byte_val));

	/*Locate the instruction I in the basic block BB*/  
	Value *inst = &(*I);
	if(corrupted_ptrs.find(I) != corrupted_ptrs.end()) return false;
	BasicBlock *BB = I->getParent();   
	BasicBlock::iterator BI;
	for(BI=BB->begin();BI!=BB->end();BI++) {
		if (BI == *I) break;
	}
	// if not found then return false.
	if(BI==BB->end()) return false;

	/*Choose the pointer operand in StoreInst and insert Corrupt function call*/
	if(StoreInst* stOp = dyn_cast<StoreInst>(inst)) 
	{
		// Has no Type
		/*Corrupt Variable*/
		args.push_back(stOp->getPointerOperand());
		if(stOp->getValueOperand()->getType()->isIntegerTy(32)) {
			CallI = CallInst::Create(func_corruptIntAdr_32bit,args,"call_corruptIntAdr_32bit",I);
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(1, corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(1));
			I->setOperand(1, corruptValPhi);
#endif
			return true;
		} else if(stOp->getValueOperand()->getType()->isIntegerTy(64)) {
			CallI = CallInst::Create(func_corruptIntAdr_64bit,args,"call_corruptIntAdr_64bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(1, corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(1));
			I->setOperand(1, corruptValPhi);
#endif
			return true;
		} else if(stOp->getValueOperand()->getType()->isFloatTy()) {
			CallI = CallInst::Create(func_corruptFloatAdr_32bit,args,"call_corruptFloatAdr_32bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(1, corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(1));
			I->setOperand(1, corruptValPhi);
#endif
			return true;
		} else if(stOp->getValueOperand()->getType()->isDoubleTy()) {
			CallI = CallInst::Create(func_corruptFloatAdr_64bit,args,"call_corruptFloatAdr_64bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(1,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(1));
			I->setOperand(1, corruptValPhi);
#endif
			return true;
		}
		return false;
	}/*end if*/

	/*Choose the pointer operand in LoadInst and insert Corrupt function call*/
	if(LoadInst *ldInst = dyn_cast<LoadInst>(inst))
	{	
		args.push_back(ldInst->getPointerOperand());
		if(inst->getType()->isIntegerTy(32)) {
			CallI = CallInst::Create(func_corruptIntAdr_32bit,args,"call_corruptIntAdr_32bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif
			return true;
		} else if(inst->getType()->isIntegerTy(64)) {
			CallI = CallInst::Create(func_corruptIntAdr_64bit,args,"call_corruptIntAdr_64bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif
			return true;
		} else if(inst->getType()->isFloatTy()) {
			CallI = CallInst::Create(func_corruptFloatAdr_32bit,args,"call_corruptFloatAdr_32bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif
			return true;
		} else if(inst->getType()->isDoubleTy()) {
			CallI = CallInst::Create(func_corruptFloatAdr_64bit,args,"call_corruptFloatAdr_64bit",I);       
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif
			return true;
		}                     
	}/*end if*/

	/*Choose the pointer operand in AllocaInst and insert Corrupt function call*/
	if(AllocaInst *allcInst = dyn_cast<AllocaInst>(inst))
	{	
		User *allcInstu = &*allcInst;
		args.push_back(allcInstu->getOperand(0));
		if(inst->getType()->isIntegerTy(32)) {
			CallI = CallInst::Create(func_corruptIntAdr_32bit,args,"call_corruptIntAdr_32bit",I);           
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif	       
			return true;
		} else if(inst->getType()->isIntegerTy(64)) {
			CallI = CallInst::Create(func_corruptIntAdr_64bit,args,"call_corruptIntAdr_64bit",I);           
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif	       
			return true;
		} else if(inst->getType()->isFloatTy()) {
			CallI = CallInst::Create(func_corruptFloatAdr_32bit,args,"call_corruptFloatAdr_32bit",I);           
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif	       
			return true;
		} else if(inst->getType()->isDoubleTy()) {
			CallI = CallInst::Create(func_corruptFloatAdr_64bit,args,"call_corruptFloatAdr_64bit",I);           
			assert(CallI);
			CallI->setCallingConv(CallingConv::C);
			Value* corruptVal = &(*CallI);
#ifdef IGNORE_20130723_CHANGES
			BI->setOperand(0,corruptVal);
#else
			PHINode* corruptValPhi = createBranchForCorruptInst(corruptVal,
				I->getOperand(0));
			I->setOperand(0, corruptValPhi);
#endif	       
			return true;
		}				
	}/*end if*/   
	return false;
}/*end InjectError_PtrError*/
/******************************************************************************************************************************/

// Use-def chain graph information
void recordUseDefChain(Module& M);

/*Dynamic Fault Injection LLVM Pass*/
namespace {
class dynfault : public ModulePass {
private:
public:
	static char ID; 
	dynfault() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {
		g_irbuilder = new IRBuilder<true, ConstantFolder, IRBuilderDefaultInserter<true> >(getGlobalContext());
		readFunctionInjWhitelist();
		errs() << "Fault injection white list read\n";
		recordUseDefChain(M);
		errs() << "Def-use chain recorded\n";
		splitBBOnCallInsts(M);
		errs() << "BBs split on CallInsts\n";
		addBBEntryCalls(M);
		
		srand(time(NULL));
		if(byte_val < 0 || byte_val > 7) 
		byte_val = rand()%8;				 
		/*Check for assertion violation(s)*/
		assert(byte_val<=7 && byte_val>=0);
		assert(ef>=0 && tf>=1 && ef<=tf);
		assert(ijo==1 || ijo==0);
		assert(print_fs==1 || print_fs==0);
		assert(ptr_err==1 || ptr_err==0);
		assert(data_err==1 || data_err==0);                
		StringRef lstr;
		Module::FunctionListType &functionList = M.getFunctionList();
		std::vector<std::string> flist = splitAtSpace(func_list);
		std::vector<std::string>::iterator vecit;

		/*Cache function references of the function defined in Corrupt.c/cpp. Also insert print_faultStatistics() 
		 * at the end ofmain() in case -pfs flag is set from the command line*/
		unsigned int j=0;
		for (Module::iterator it = functionList.begin(); it != functionList.end(); ++it,j++) {
			lstr = it->getName();
			cstr = lstr.str();                                        
			if (cstr.find("isNextFaultInThisBB") != std::string::npos) {
				func_isNextFaultInThisBB = &*it; continue;
			} if(cstr.find("print_faultStatistics")!=std::string::npos){
				func_print_faultStatistics =&*it; continue;
			} if(cstr.find("corruptIntData_16bit")!=std::string::npos) {
				func_corruptIntData_16bit =&*it; continue;
			} if(cstr.find("corruptIntData_32bit")!=std::string::npos) {
				func_corruptIntData_32bit =&*it; continue;
			} if(cstr.find("corruptIntData_64bit")!=std::string::npos) {
				func_corruptIntData_64bit =&*it; continue;
			} if(cstr.find("corruptIntData_8bit")!=std::string::npos) {
				func_corruptIntData_8bit =&*it; continue;
			} if(cstr.find("corruptFloatData_32bit")!=std::string::npos) {
				func_corruptFloatData_32bit =&*it; continue;
			} if(cstr.find("corruptFloatData_64bit")!=std::string::npos) {
				func_corruptFloatData_64bit =&*it; continue;
			} if(cstr.find("corruptFloatData_80bit")!=std::string::npos) {
				func_corruptFloatData_80bit =&*it; continue;
			} if(cstr.find("corruptIntAdr_32bit")!=std::string::npos) {
				func_corruptIntAdr_32bit =&*it; continue;
			} if(cstr.find("corruptIntAdr_64bit")!=std::string::npos) {
				func_corruptIntAdr_64bit =&*it; continue;
			} if(cstr.find("corruptFloatAdr_32bit")!=std::string::npos) {
				func_corruptFloatAdr_32bit =&*it; continue;
			} if(cstr.find("corruptFloatAdr_64bit")!=std::string::npos) {
				func_corruptFloatAdr_64bit =&*it; continue;
			} if(cstr.find("incrementFaultSiteCount")!=std::string::npos) {
				func_incrementFaultSitesEnumerated =&*it; continue;                            
			} if(cstr.find("__printInstCount")!=std::string::npos) {
				func_printInstCount = &*it; continue;
			} if(cstr.find("initializeFaultInjectionCampaign")!=std::string::npos) {
				func_initFaultInjectionCampaign = &*it; continue;
			} if(cstr == "main") {
				func_main = &*it; continue;
			} if(!isFunctionNameBlacklisted(cstr.c_str())) {
				if(print_fs) {
					assert(func_print_faultStatistics);
					Function *Fmain = it;	
					inst_iterator Imain,INmain,Emain;
					Imain=inst_begin(Fmain);
					INmain=Imain;
					INmain++;
					for(Emain=inst_end(Fmain);INmain!=Emain;Imain++,INmain++);
					Value *inst = &(*Imain);
					std::vector<Value*> args;
					args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ijo));
					args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),ef));
					args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),tf));
					args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()),byte_val));
					if(isa<ReturnInst>(inst)) {
						Instruction* Im = &(*Imain);
						CallInst* CallI = CallInst::Create(func_print_faultStatistics,args,"call_print_faultStatistics",Im);
						CallI->setCallingConv(CallingConv::C);
					} else {
						 Instruction* Im = &(*Imain);
						 BasicBlock *BBm = Im->getParent();
						 CallInst* CallI = CallInst::Create(func_print_faultStatistics,args,"call_print_faultStatistics",BBm);
						 CallI->setCallingConv(CallingConv::C);
					}
				}
				continue;                           
			}          
		}/*end for*/
						
		/* Cache instructions from all the targetable functions for fault injection in case func list is not
		 * defined by the use. If func list if defined by the use then cache only function defined by the user*/         
		for (Module::iterator it = functionList.begin(); it != functionList.end(); ++it,j++){ 
			lstr = it->getName();
			cstr = lstr.str();   	 	            
			if(cstr.find("print_faultStatistics")!=std::string::npos  ||
				cstr.find("corruptIntData_8bit")!=std::string::npos   ||
				cstr.find("corruptIntData_16bit")!=std::string::npos   ||
				cstr.find("corruptIntData_32bit")!=std::string::npos   ||
				cstr.find("corruptIntData_64bit")!=std::string::npos   ||
				cstr.find("corruptFloatData_32bit")!=std::string::npos ||
				cstr.find("corruptFloatData_64bit")!=std::string::npos ||
				cstr.find("corruptIntAdr_32bit")!=std::string::npos    ||
				cstr.find("corruptIntAdr_64bit")!=std::string::npos    ||
				cstr.find("corruptFloatAdr_32bit")!=std::string::npos  ||
				cstr.find("corruptFloatAdr_64bit")!=std::string::npos  ||
				isFunctionNameBlacklisted(cstr.c_str()) )
				continue;
			Function *F=NULL;
			bool is_in_whitelist = true;
			/*if the user defined function list is empty or the currently selected function is in the list of
			 * user defined function list then consider the function for fault injection*/
			if(!func_list.compare("") || std::find(flist.begin(), flist.end(), cstr)!=flist.end()) {
				F = it;
				if(!shouldInjectFunction(F)) is_in_whitelist = false;
			} else {
				continue;
			}
			if(F->begin()==F->end())
				continue;

			/*Cache instruction references with in a function to be considered for fault injection*/             
			std::map<BasicBlock*, std::set<Instruction*> > ilist;
			for(Function::iterator fi = F->begin(); fi!=F->end(); fi++) {
				BasicBlock& BB = *fi;
				BasicBlock* pBB = &BB;
				ilist[pBB] = std::set<Instruction*>();
				unsigned vuln = 0;
				if(is_in_whitelist) {
					for(BasicBlock::iterator bi = BB.begin(); bi!=BB.end(); bi++) {
						unsigned vuln_delta = 0;
						Instruction* I = &(*bi);
						Value *in = &(*I);  
						Instruction* p_in = &*I;
						if(in == NULL) continue;
						if(data_err) {
							if(isa<BinaryOperator>(in) || 
								isa<CmpInst>(in)       ||
								isa<StoreInst>(in)     ||
								isa<LoadInst>(in))
							{
								ilist[pBB].insert(p_in);
								vuln_delta = 1;
							}
						}
						if(ptr_err) {
							if(isa<StoreInst>(in) || 
							isa<LoadInst>(in)  ||
							isa<CallInst>(in)  ||
							isa<AllocaInst>(in)) 
							{
								ilist[pBB].insert(p_in);
								vuln_delta = 1;
							}
						}
						vuln += vuln_delta;
					}

					// declare an i1 @ beginning of BB
#ifndef IGNORE_20130723_CHANGES
					if(vuln > 0)				
					{
						Instruction* first = getFirstNonPHINonLandingPad(pBB);
						std::vector<Value*> args;
						CallInst* pred = CallInst::Create(func_isNextFaultInThisBB,
							args, "isNextFaultInThisBB", first);
						bb_to_pred[pBB] = pred;
					}
#endif
				}
			}
			/*Check if instruction list is empty*/
			if(ilist.empty())
				continue;

			// Change on 20130723: Using predicate; may save C.P.U. time
			// Adverse side effect #1: will break a BasicBlock::iterator
			// luckily, we're not using a BasicBlock::iterator. 
			std::map<BasicBlock*, std::set<Instruction*> >::iterator itrBBI;
			for(itrBBI = ilist.begin(); itrBBI != ilist.end(); itrBBI++) {
				BasicBlock* pBB = itrBBI->first;
				std::set<Instruction*> theSet = itrBBI->second;
				unsigned bb_fs_count = 0;
				for(std::set<Instruction*>::iterator itr = theSet.begin(); itr != theSet.end(); itr++) {
					fprintf(stderr, "%d faults injected\r", g_fault_index);
//					Instruction* inst = *(ilist.begin());
					Instruction* inst = *itr;
					if(ptr_err) {
						g_fault_index++;
						if(InjectError_PtrError_Dyn(inst, g_fault_index)) {
							injected_fault_indices.insert(g_fault_index);
							bb_fs_count++;
						}
					}
					if(data_err) {
						g_fault_index++;
						if(InjectError_DataReg_Dyn(inst, g_fault_index)) {
							injected_fault_indices.insert(g_fault_index);
							bb_fs_count++;
						}
					}               
				}
				bb_fs_counts[pBB] = bb_fs_count;
			}
		}

		/* Now I am going to split the BB's
		 * So the counts should only be -approximate-
		 * The # of fault sites is added at the beginning of a BB
		 */
		appendInstCountCalls(M);
		
		// Insert call to initialize fault injection campaign if there's main()
		//   when the injected program starts
		if(func_main)
		{
			BasicBlock* b = ((Function*)(func_main))->begin();
			Instruction* first = b->begin();
			
			std::vector<Value*> args;
			args.push_back(ConstantInt::get(IntegerType::getInt32Ty(getGlobalContext()), ef));
			args.push_back(ConstantInt::get( IntegerType::getInt32Ty(getGlobalContext()), tf));

			CallInst* call_init = CallInst::Create(func_initFaultInjectionCampaign,
				args, "", first);
			assert(call_init);
		}

		// Print out fault site statistics.
		writeFaultSiteDOTGraph();

		return false;
	}/*end function definition*/
};/*end class definition*/
}/*end namespace*/

char dynfault::ID = 0;
static RegisterPass<dynfault> F0("dynfault", "Dynamic Fault Injection emulating transient hardware error behavior");
/******************************************************************************************************************************/

/*Prints static fault injection statistics*/
void printStat(unsigned int indexloc, bool inst_flag, bool func_flag) {
	if(!func_flag)
	{
		errs()<<"#################################################"<< '\n';
		errs()<<"Error: Couldn't select a valid function" << '\n';
		errs()<<"#################################################"<< '\n';
	} else {
		if(inst_flag) {
			errs()<<"#################################################"<< '\n';
			errs()<<"Error injected in the function: "<< cstr <<'\n';
			errs()<<"Error injected in the instruction at position " << indexloc <<'\n' ;
			errs()<<"Number of instruction in the function: " << lstsize <<'\n' ;
			errs()<<"Successfully inserted fault!!" << '\n';            
			errs()<<"#################################################"<< '\n';
		} else {
			errs()<<"#################################################"<< '\n';
			errs()<<"Error: Couldn't select a valid instruction" << '\n';
			errs()<<"#################################################"<< '\n';
		}
	}
}

/*Injects static fault(s) into data register*/
bool InjectError_DataReg(Instruction *I) {
	/*generate random probablity and check it against user defined probablity*/
	int p=(rand()%tf)+1;
	if(p>ef)        
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
	int p=(rand()%tf)+1;
	if(p>ef)        
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
	if(StoreInst *stInst = dyn_cast<StoreInst>(inst)) { 
		Value *top = &(*(stInst->getPointerOperand())); 
		
		Value* iAddr = new PtrToIntInst(stInst->getPointerOperand(),
			IntegerType::getInt64Ty(getGlobalContext()),
			top->getName(),
			stInst
			);
		if(!iAddr) assert(0 && "Create PtrToInt inst error. This should not happen!");

		Value *tVal = ConstantInt::get(IntegerType::getInt64Ty(getGlobalContext()), mask);
 
		BinaryOperator *N = BinaryOperator::Create(Instruction::And,
			tVal, iAddr, top->getName(), BI);

		Value* corruptedAddr = new IntToPtrInst(N,
			stInst->getPointerOperand()->getType(),
			top->getName(),
			stInst
			);

		BI->setOperand(1, corruptedAddr); /* 1? */
		return true;
	}/*end if*/

	/*Check if I is of type LoadInst and inject error if true*/
	if(LoadInst *ldInst = dyn_cast<LoadInst>(inst)) { 
		// LLVM says we can't cast an int32* to an integer.

//    IntegerType* iTy = cast<IntegerType>(ldInst->getPointerOperand()->getType());
		Value *top = &(*(ldInst->getPointerOperand()));

		Value* iAddr = new PtrToIntInst(ldInst->getPointerOperand(),
			IntegerType::getInt64Ty(getGlobalContext()),
			top->getName(),
			ldInst
			);
		if(!iAddr) assert(0 && "Create Ptr To Int Inst Error");

//    Value *tVal=ConstantInt::get(ldInst->getPointerOperand()->getType(),mask);
		Value *tVal = ConstantInt::get(IntegerType::getInt64Ty(getGlobalContext()), mask);
			
//    BinaryOperator *N = BinaryOperator::Create(Instruction::And, 
//        tVal, ldInst->getPointerOperand(), top->getName(), BI);
		BinaryOperator *N = BinaryOperator::Create(Instruction::And,
				tVal, iAddr, top->getName(), BI);

		Value* corruptedAddr = new IntToPtrInst(N,
			ldInst->getPointerOperand()->getType(),
			top->getName(),
			ldInst
			);

		BI->setOperand(0, corruptedAddr);

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
		Type* calledTy = callInst->getCalledValue()->getType();
		Value *top = &(*(callInst->getCalledValue()));  
		if(isa<PointerType>(calledTy)) {
			Value* iAddr = new PtrToIntInst(callInst->getCalledValue(),
					IntegerType::getInt64Ty(getGlobalContext()),
					top->getName(),
					callInst
				);
			if(!iAddr) assert(0);
			Value* tVal = ConstantInt::get(IntegerType::getInt64Ty(getGlobalContext()),
				mask);
			BinaryOperator *N = BinaryOperator::Create(Instruction::And, 
				tVal, iAddr, top->getName(), BI);
			Value* corruptedCalledValue = new IntToPtrInst(N,
				calledTy,
				top->getName(),
				callInst
				);
			callInst->setCalledFunction(corruptedCalledValue);
			return true;  
		} else {
			Value *tVal=ConstantInt::get(callInst->getCalledValue()->getType(),mask);
			BinaryOperator *N = BinaryOperator::Create(Instruction::And, 
				tVal, callInst->getCalledValue(), top->getName(), BI);       
			
			// Is the code supposed to change the object on which the function is
			//   called ?
			// BI->setOperand(0, N);
			callInst->setCalledFunction(N);
			return true;
		}
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
/******************************************************************************************************************************/

/*Static Fault Injection LLVM Pass*/
namespace {
	class staticfault : public ModulePass 
	{
		public:
			static char ID; 
			staticfault() : ModulePass(ID) {}	                
			virtual bool runOnModule(Module &M) {
				assert(0); // Disabled for the moment. June 26
				srand(time(NULL));
				if(byte_val < 0 || byte_val > 7) 
					byte_val = rand()%8;
						/*Check for assertion violation(s)*/
				assert(byte_val<=7 && byte_val>=0);
				assert(ef>=0 && tf>=1 && ef<=tf);
				assert(ijo==1 || ijo==0);
				assert(print_fs==1 || print_fs==0);
				assert(ptr_err==1 || ptr_err==0);
				assert(data_err==1 || data_err==0);                
				bool func_flag=false;
				bool insert_flag=false;
				StringRef lstr;                
				Module::FunctionListType &functionList = M.getFunctionList();
				unsigned int j=0;
				/*Cache function references to be considered for fault injection*/
				for (Module::iterator it = functionList.begin(); it != functionList.end(); ++it,j++) {
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
					for(inst_iterator I=inst_begin(F),E=inst_end(F);I!=E;I++) {
						Value *in = &(*I);
						if(data_err)
						if(isa<BinaryOperator>(in) || 
							isa<CmpInst>(in)) {                     
							ilist.insert(&*I);
						}
						if(ptr_err)
							if(isa<StoreInst>(in) || 
							   isa<LoadInst>(in)  ||
							   isa<CallInst>(in)  ||
							   isa<AllocaInst>(in)) {                     
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
					for(std::set<Instruction*>::iterator its =ilist.begin();its!=ilist.end();its++,i++) {
						if(r==i) {
							Instruction* inst = *its;
							if(data_err && !inst->mayReadOrWriteMemory())
								if(InjectError_DataReg(inst))
									insert_flag=true;                             
							if(ptr_err && inst->mayReadOrWriteMemory())
								if(InjectError_PtrError(inst))
									insert_flag=true;                              
							if(insert_flag) {
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

const char* getMyTypeName(const Value* v) {
	if(isa<BinaryOperator>(v)) {
		return "BinOp";
	} else if(isa<CmpInst>(v)) {
		return "Cmp";
	} else if(isa<StoreInst>(v)) {
		return "ST";
	} else if(isa<LoadInst>(v)) {
		return "LD";
	} else if(isa<GetElementPtrInst>(v)) {
		return "GEP";
	} else if(isa<ReturnInst>(v)) {
		return "Ret";
	} else if(isa<BranchInst>(v)) {
		return "Br";
	} else if(isa<PHINode>(v)) {
		return "Phi";
	} else if(isa<CallInst>(v)) {
		return "Call";
	} else if(isa<ICmpInst>(v)) {
		return "ICmp";
	} else if(isa<AllocaInst>(v)) {
		return "Alloca";
	} else return "--";
}
