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
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/ArrayRef.h"

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

  	// Skeleton from:
	//https://www.inf.ed.ac.uk/teaching/courses/ct/17-18/slides/llvm-2-writing_pass.pdf
		
	int bbCounter = 0;
	int first_time = 1;
	int* edge_count = NULL;

	// First time, go through and count all the blocks
	// Second time, go through and initialize the basic block array with edge counts

	while (first_time)
	{
		if (bbCounter > 0 && first_time == 1)
		{
			first_time = 0;
			edge_count = new int[bbCounter];

			for (int i=0; i<bbCounter; i++) {
			    edge_count[i] = 0; // Initialize all elements to zero.
			}
			errs() << "Second time." << "\n";

			/* Debug print
			for (int i = 0; i < bbCounter; i++)
			{
				errs() << edge_count[i] << ",";
			}*/
			bbCounter = 0;
			
		}

		errs() << "Function: " << F.getName() <<"\n";

		for (Function::iterator bb = F.begin(), e=F.end(); bb != e; bb++)
		{

			// THIS LEVEL ITERATES THROUGH BASIC BLOCKS
			errs() << "BB: " << bbCounter <<"\n";
			errs() << "dump" << "\n";
			bb->dump();
			for (BasicBlock::iterator i = bb->begin(), e = bb->end(); i!=e; i++)
			{
				// THIS LEVEL ITERATES THROUGH INSTRUCTIONS

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
			
			// This goes through and updates the edge_count array
			if (first_time == 0)
			{
				edge_count[bbCounter] = edge_count[bbCounter] + 1;
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


	}

	// This prints the edge_count
	errs() << "\n";
	errs() << "edge_count contents: \n";
	for (int i = 0; i < bbCounter; i++)
	{
		errs() << edge_count[i] << ",";
	}

	delete edge_count;
	
	return false;

	  //return true;
	} // end runOnFunction


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
*/

  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

