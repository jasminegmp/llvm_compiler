/*
 * Authors: Name(s) <email(s)>
 * 
 */

/*
Question
1. why global variable set that way in sample code? why not just use some C global variable construct?

*/

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"

#include "llvm/IR/Dominators.h"
/*
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"*/

using namespace llvm;

namespace {
  struct CS201PathProfiling : public FunctionPass {
  /*std::map<std::string,int> opCounter;
  
  void getAnalysisUsage(AnalysisUsage &AU) const{
	AU.addRequired<LoopInfo>();
	AU.setPreservesAll();
  } */
  	static char ID;
  	//GlobalVariable *DomSet = NULL;
    CS201PathProfiling() : FunctionPass(ID) {}

	//----------------------------------
	bool doInitialization(Module &M) {
		int bbCounter = 0;
		//LLVMContext *Context;
		bool dom;
		//int* DomSet = NULL; 
		//std::string* DomArray = NULL;

		// never got this one working... but keeping it in for now
		//DomSet =  new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), false, GlobalValue::InternalLinkage, 0, "DomSet);
 	
     	errs() << "Module: " << M.getName() << "\n";
 

		errs() << "\n---------Starting BasicBlockDemo---------\n";
	
		// Loops through functions
		for (Module::iterator func = M.begin(), y = M.end(); func != y; ++func)
		{ 
			errs() << "Function: " << func->getName() <<"\n"; // print out function numbers
			
			// First draw dominator tree
			DominatorTree domtree;
			domtree.recalculate(*func);

			// Loops through basic blocks
			for (Function::iterator bb = func->begin(), e=func->end(); bb != e; ++bb)
			{

				//errs() << "BB " << bbCounter << " addr: "<< BlockAddress::get(bb) <<"\n";
				errs() << "BasicBlock " << bbCounter <<"\n";
				bb->printAsOperand(errs(), false);
				bb->dump();
				bbCounter += 1;
				//bb->getTerminator();
				
				errs() << "num of successors: " << bb->getTerminator()->getNumSuccessors() <<"\n";
				
				// Loops through each successor
				 for (unsigned int i = 0; i < bb->getTerminator()->getNumSuccessors(); i++)
				 {

				 	//errs() << "Succ:" << bb->getTerminator()->getSuccessor(i) <<"\n";
				 	dom = domtree.dominates(bb->getTerminator()->getSuccessor(i)->getTerminator(), bb->getFirstInsertionPt());
				 	errs () << "bool result: " << dom << "\n";
				 	if (dom) // is a back edge
				 	{
				 		errs() << "Found a back edge!";
				 		bb->getTerminator()->getSuccessor(i)->printAsOperand(errs(), false);
				 		errs() << " dominates ";
				 		bb->printAsOperand(errs(), false);
				 		errs() << "\n";
						auto backedge = std::make_pair(bb,bb->getTerminator()->getSuccessor(i)); 
						//errs() << "BACKEDGE" << std::get<0>(backedge) << "\n"; 
				 	}
				 	else // is not a back edge
				 	{
				 		bb->printAsOperand(errs(), false);
				 		errs() << " dominates ";
				 		bb->getTerminator()->getSuccessor(i)->printAsOperand(errs(), false);		 		
				 		errs() << "\n";

				 	}
				 }

				 // now go find all loops based off backedge
				 errs() << "\n";

			}
		}

	
		return false;
	}

	//----------------------------------
	bool doFinalization(Module &M) {
	  return false;
	}
	
	//----------------------------------
	bool runOnFunction(Function &F) override {
/*
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
				BasicBlock* B = bb;
				for (auto it = pred_begin(B), et = pred_end(B); it != et; ++it)
				{
				  BasicBlock* predecessor = *it;
				  errs() << "pred" << &predecessor << "\n";
				}
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
		errs() << edge_count[i] << " ";
	}
	errs() << "\n";

	delete edge_count;

	return false;
*/

	return true;
	} // end runOnFunction
  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

