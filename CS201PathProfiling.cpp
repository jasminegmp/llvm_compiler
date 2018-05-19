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
#include <stack>

#include "llvm/IR/Dominators.h"
/*
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"*/

using namespace llvm;

namespace {
  struct CS201PathProfiling : public FunctionPass {
  	static char ID;
    CS201PathProfiling() : FunctionPass(ID) {}

	//----------------------------------
	bool doInitialization(Module &M) {
		bool dom;
		std::stack <BasicBlock*> stack;
		std::pair <BasicBlock*, BasicBlock*> backedge_pair;
		std::vector<std::pair<BasicBlock*, BasicBlock*>> backedge_vector; 

		// never got this one working... but keeping it in for now
		//DomSet =  new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), false, GlobalValue::InternalLinkage, 0, "DomSet);
 	
     	errs() << "Module: " << M.getName() << "\n";

		errs() << "\n---------Starting BasicBlockDemo---------\n";
	
		//if (/* condition */)
		{


			// Loops through functions
			for (Module::iterator func = M.begin(), y = M.end(); func != y; ++func)
			{ 
				errs() << "\n---------Start of function ---------\n";
				int bbCounter = 0;
				int backedge_count = 0;
				errs() << "Function: " << func->getName() <<"\n"; // print out function numbers
				
				// First draw dominator tree
				DominatorTree domtree;
				errs() << "Function: " << func->getName() << *func <<"\n"; // print out function numbers
				
				// hacked this from this source: https://stackoverflow.com/questions/23929468/identifying-user-define-function-through-llvm-pass
				if(func->size()>0)
				{
					domtree.recalculate(*func);
				}
				
				errs() << "Function: " << func->getName() <<"\n"; // print out function numbers
				// Loops through basic blocks
				for (Function::iterator bb = func->begin(), e=func->end(); bb != e; ++bb)
				{
					errs() << "BasicBlock " << bbCounter <<"\n";
					bb->printAsOperand(errs(), false);
					bb->dump();
					bbCounter += 1;
					
					errs() << "Num of successors: " << bb->getTerminator()->getNumSuccessors() <<"\n";
					
					// Loops through each successor
					 for (unsigned int i = 0; i < bb->getTerminator()->getNumSuccessors(); i++)
					 {

					 	//errs() << "Succ:" << bb->getTerminator()->getSuccessor(i) <<"\n";
					 	dom = domtree.dominates(bb->getTerminator()->getSuccessor(i)->getTerminator(), bb->getFirstInsertionPt());
					 	errs () << "bool result: " << dom << "\n";
					 	if (dom && (bb->getTerminator()->getNumSuccessors() > 0)) // is a back edge
					 	{
					 		//errs() << "Found a back edge!";
					 		bb->getTerminator()->getSuccessor(i)->printAsOperand(errs(), false);
					 		//errs() << " dominates ";
					 		bb->printAsOperand(errs(), false);
					 		//errs() << "\n";

					 		// now add back edge onto list of backedges
					 		// pair is <N, D>
							backedge_pair = std::make_pair(bb->getTerminator()->getSuccessor(i),bb); 

							backedge_vector.push_back(backedge_pair);
							backedge_count += 1;
							
							//errs() << "-----------VECTOR SIZE:" << backedge_vector.size();
					 	}
					 	else // is not a back edge
					 	{
					 		bb->printAsOperand(errs(), false);
					 		errs() << " dominates ";
					 		bb->getTerminator()->getSuccessor(i)->printAsOperand(errs(), false);		 		
					 		errs() << "\n";

					 	}

					 } // end of successor loop

				} // end of basic block loop
				/*
				for (int j = 0; j < backedge_count; j++)
				{
					errs() << "BACK EDGES ARE: " << backedge_vector[0].first << "\n";
					errs() << "BACK EDGES ARE: " << backedge_vector[0].second << "\n";

				}*/
				errs() << "BACK EDGES count: " << backedge_count << "\n";


				/*errs() << "--------STACK SIZE" << stack.size();
				errs() << "\n";*/

				//errs() << "--------TOP OF STACK" << stack.top();
				//errs() << "\n";

				///////////////// Loop Algorithm //////////////////////////////////////
				// now go find all loops based off backedge

				// loop through backedge list
				while(backedge_count--)
				{
					// create an empty stack
					std::stack <BasicBlock*> stack;

					// remember pair is <N,D>
					// create a loop vector
					std::vector<BasicBlock*> loop_vector; 
					// insert D into loop vector
					loop_vector.push_back(backedge_vector[backedge_count].first);

					// insert n onto stack
					stack.push(backedge_vector[backedge_count].second);
					BasicBlock * original_sink = backedge_vector[backedge_count].second;
					/*
					errs() << "--------FIRST - TOP OF STACK" << stack.top();
					errs() << "\n";

					errs() << "--------SECOND - Loop VECTOR" << loop_vector[0];
					errs() << "\n";*/

					// while stack is not empty
					while (!stack.empty())
					{
						// pop the top element of stack
						BasicBlock * top_obj = stack.top();
						stack.pop();

						errs() << "Popped top element of the stack, BB:  ";
						top_obj->printAsOperand(errs(), false);
						errs() << "\n";

						// if not in loop vector, insert top obj into stack
						// referred to this https://stackoverflow.com/questions/571394/how-to-find-out-if-an-item-is-present-in-a-stdvector
						if (std::find(loop_vector.begin(), loop_vector.end(), top_obj) != loop_vector.end() )
						{
							
						}
						else
						{
							loop_vector.push_back(top_obj);
						}
						

						// find all predecessors of the top element of the stack.
						// referred to this https://stackoverflow.com/questions/21708209/get-predecessors-for-basicblock-in-llvm
						for (auto it = pred_begin(top_obj), et = pred_end(top_obj); it != et; ++it)
						{
							BasicBlock* predecessor = *it;
							errs() << "predecessor BB:  ";
							predecessor->printAsOperand(errs(), false);
							errs() << "\n";

							// if not in loop vector, insert pred into stack
							// referred to this https://stackoverflow.com/questions/571394/how-to-find-out-if-an-item-is-present-in-a-stdvector
							if (std::find(loop_vector.begin(), loop_vector.end(), predecessor) != loop_vector.end() )
							{
								errs() << "IN LOOP \n";
							}
								// do nothing
							else if (predecessor != original_sink) // make sure also pred != original sink
							{
								errs() << "NOT IN LOOP \n";
								loop_vector.push_back(predecessor);
								//push pred onto the stack
								stack.push(predecessor);
							}
							else
							{
								loop_vector.push_back(predecessor);
								//push pred onto the stack
							}
							
						}
					}


				// print out loop contents
				errs() << "/////////////////////////////////\n\n";	
				errs() << "Loop Found : " << "\n";
				for (unsigned int i = 0; i < loop_vector.size(); i++)
				{
					BasicBlock* loopitem = loop_vector[i];
					loopitem->printAsOperand(errs(), false);
					errs() << ",";
				}
				errs() << "\n";
				} // end of function loop
				errs() << "/////////////////////////////////\n\n";

		}/*
			std::vector<std::pair<BasicBlock*, BasicBlock*>>().swap(backedge_vector);
			std::vector<std::pair<BasicBlock*, BasicBlock*>>().swap(backedge_vector);
			std::vector<BasicBlock*>().swap(backedge_vector); 

					std::stack <BasicBlock*> stack;
			std::pair <BasicBlock*, BasicBlock*> backedge_pair;
			std::vector<std::pair<BasicBlock*, BasicBlock*>> backedge_vector;*/ 
			//std::vector<BasicBlock*>().swap(backedge_vector); 
			//backedge_vector.swap(std::vector<BasicBlock*>());

			//free up everything
			std::vector<std::pair<BasicBlock*, BasicBlock*>>(backedge_vector).swap(backedge_vector);
			std::stack <BasicBlock*>(stack).swap(stack);
			std::pair <BasicBlock*, BasicBlock*>(backedge_pair).swap(backedge_pair);

			//std::vector <BasicBlock*>(loop_vector).swap(loop_vector);
			//std::vector<BasicBlock*> loop_vector; 
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

	return false;
	} // end runOnFunction
  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

