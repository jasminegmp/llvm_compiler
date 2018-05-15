/*
 * Authors: Name(s) <email(s)>
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"

using namespace llvm;

namespace {
  struct CS201PathProfiling : public FunctionPass {
  std::map<std::string,int> opCounter;
  static char ID;
  CS201PathProfiling() : FunctionPass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const{
	AU.addRequired<LoopInfo>();
	AU.setPreservesAll();
  }

	//----------------------------------
	bool doInitialization(Module &M) {
	
	  return false;
	}

	//----------------------------------
	bool doFinalization(Module &M) {
	  return false;
	}
	
	//----------------------------------
	bool runOnFunction(Function &F) override {
/*
	LoopInfo &LI = getAnalysis<LoopInfo>();
	int loopCounter = 0;
	errs()<<F.getName()+"\n";
	for(LoopInfo::iterator i = LI.begin(), e=LI.end(); i!=e; ++i){
		Loop *L = *i;
		int bbCounter = 0;
		loopCounter++;
		for(Loop::block_iterator bb = L->block_begin(); bb!= L->block_end(); ++bb){
			bbCounter+=1;
		}	
		errs()<<"Loop ";
		errs()<<loopCounter;
		errs()<<":#BBs =";
		errs()<<bbCounter;
		errs()<<"\n";
	}
	return(false);
*/  // Skeleton from:
	//https://www.inf.ed.ac.uk/teaching/courses/ct/17-18/slides/llvm-2-writing_pass.pdf
		
	int bbCounter = 0;

	errs() << "Function: " << F.getName() <<"\n";

	for (Function::iterator bb = F.begin(), e=F.end(); bb != e; bb++)
	{
		errs() << "BB: " << bbCounter <<"\n";
		errs() << "dump" << "\n";
		bb->dump();
		for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i!=e; i++)
		{

			if (opCounter.find(i->getOpcodeName()) == opCounter.end())
			{
				opCounter[i->getOpcodeName()] = 1;
			} 
			else
			{
				opCounter[i->getOpcodeName()] += 1;
			}
			//errs() << *i <<"\n";
		}
		bbCounter+=1;
	}

	errs() << "The following is number of operations info:" << "\n";
	std::map <std::string, int>::iterator i = opCounter.begin();
	std::map <std::string, int>::iterator e = opCounter.end();

	while(i != e)
	{
		errs() << i->first << ": " << i->second << "\n";
		i++;
	}

	errs() << "\n";
	opCounter.clear();

	errs() << "Number of basic blocks:" << bbCounter << "\n";
	
	return false;

	  //return true;
	} // end runOnFunction

  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

