#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include <map>
#include <set>
#include <stack>
#include "llvm/IR/Dominators.h"
#include <algorithm>

using namespace llvm;
using namespace std;


namespace {

  static Function* printf_prototype(LLVMContext& ctx, Module *mod) {

      std::vector<Type*> printf_arg_types;
      printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
      FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
      Function *func = mod->getFunction("printf");
      if(!func)
        func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
      func->setCallingConv(CallingConv::C);
      return func;
    }

    struct CS201Profiling : public FunctionPass 
    {

    static char ID;
    LLVMContext *Context;
    Function *printf_func = NULL;

    GlobalVariable *bbCounter = NULL;
    GlobalVariable *previousBlockID = NULL;
    GlobalVariable *BasicBlockPrintfFormatStr = NULL;
    GlobalVariable *pathCounter = NULL;
   
    //FuncNameToBlockNumber is a map from string (function name) to another map which connects to blocknum which is blocks name and their indices :{b0:0,b1:1,..};
    map<string, map<string,int>> FuncNameToBlockNumber;  
    //edgeCounter is a map from the function name(string) to the address(string)
    map<string,GlobalVariable*> edgeCounter;  
    //FuncNameToEdges is a map from function name(string) to a set of pairs
    map<string, set<pair<string,string>>> FuncNameToEdges;  

    //hash map of edge values
    map<std::pair<BasicBlock*, BasicBlock*>,int> EdgeValueMap; 

    // nested vector of innermost loops in topological order
	std::vector<std::vector<BasicBlock*>> topo_loop_vector;
	std::vector<int> totNumPath;


    CS201Profiling() : FunctionPass(ID) {}

    // This function goes and finds the edge weights
    void findEdgeProfiling(std::vector<std::vector<BasicBlock*>> topo_loop_vector)
    {
    	map<BasicBlock*, int> NumPathsMap;
    	BasicBlock* currentBB;

    	errs() << "Edge values:\n";
    	
    	// debug printing

    	// This loops through innerloop vector
    	for (unsigned int i = 0; i < topo_loop_vector.size(); i++)
		{
			// This loops through nested innerloop vecotr
			for (unsigned int j = 0; j < topo_loop_vector[i].size(); j++)
			{
				currentBB = topo_loop_vector[i][j];

				if(j == 0)
					NumPathsMap[currentBB] = 1;
				else
				{
					NumPathsMap[currentBB] = 0;
					//go through each success of bb
					// add to map
					/*errs() << "Successors\n"; */
					for (unsigned int k = 0; k < currentBB->getTerminator()->getNumSuccessors(); k++)
				 	{
				 		BasicBlock* successorBB = currentBB->getTerminator()->getSuccessor(k);
				 		if(std::find(topo_loop_vector[i].begin(), topo_loop_vector[i].end(), successorBB) != topo_loop_vector[i].end())
				 		{
					 		
					 		EdgeValueMap[make_pair(currentBB, successorBB)] = NumPathsMap[currentBB];
					 		
					 		successorBB->printAsOperand(errs(), false);
					 		NumPathsMap[currentBB] = NumPathsMap[currentBB] + NumPathsMap[successorBB];
					 		//errs() << EdgeValueMap<currentBB, successorBB>;
				 		}

				 	}

				}
				errs() << "J:" << j << "\n";
				errs() << "NumPathsMap: " << NumPathsMap[currentBB] << "\n";
				/*
				errs() << "\nprinting numpaths\n"; 
				currentBB->printAsOperand(errs(), false);
				errs() << ":" << NumPathsMap[currentBB] << "\n";*/
				
				// find number of paths

				if (j >= (topo_loop_vector[i].size() - 1))
				{
					//errs() << "totNumPath[i]: " << NumPathsMap[currentBB] << "\n";
					totNumPath.push_back(NumPathsMap[currentBB]);
				}
			} // end nested innerloop vector
			//totNumPath[i] = NumPathsMap[topo_loop_vector[i][0]];
			
		} // end innerloop vector

		// following is printing for just debug reasons
		for(std::map<std::pair<BasicBlock*, BasicBlock*>,int>::iterator iter = EdgeValueMap.begin(); iter != EdgeValueMap.end(); ++iter)
		{
			BasicBlock* bb1 = iter->first.first;
			BasicBlock* bb2 = iter->first.second;
			int v =  iter->second;
			errs() << "{";
			bb1->printAsOperand(errs(), false);
			//errs() << "->BB2:";
			errs() << ",";
			bb2->printAsOperand(errs(), false);
			errs() << ",";
			errs() << v;
			errs() << "}" << "\n";;

		}
		/*
		errs() << "path vector output\n";
		for(unsigned int z = 0; z < totNumPath.size(); z++)
		{

			errs() << totNumPath[z] << ",";

		}
		errs() << "\n";	*/
    }// END of findEdgeProfiling

    // This function goes and finds the topological ordering of the loop vector
    void topologicalOrdering(std::vector<std::vector<BasicBlock*>> innerloop_vector)
    {
    	
    	//errs() << "Sorting in reverse topological order!\n";
    	// debug printing

		// go through each vertex in topological order
		// NOTE: topological order is kind of kept when finding the loop
		// but because the loop is created using the back edges, to
		// keep the topological order, you must start with index 1 to end
		// and then go back to index 0 
		// example loop_vector = [2,7,6,5,4], then you start with index 1
		// to the end, and then back to index 0 to get 7,6,5,4,2

    	// This loops through innerloop vector
    	for (unsigned int i = 0; i < innerloop_vector.size(); i++)
		{
			std::vector<BasicBlock*> temp_vector;
			// This loops through nested innerloop vecotr
			for (unsigned int j = 1; j < innerloop_vector[i].size(); j++)
			{
				BasicBlock* loopitem = innerloop_vector[i][j];
				temp_vector.push_back(loopitem);
				//BasicBlock* loopitem = topo_loop_vector[i][j-1];
				//loopitem->printAsOperand(errs(), false);
				//errs() << ",";
			} // end nested innerloop vector
			//topo_loop_vector[i].push_back(innerloop_vector[i][0]);
			temp_vector.push_back(innerloop_vector[i][0]);
			topo_loop_vector.push_back(temp_vector);
		} // end innerloop vector

    } // END of topologicalOrdering

    // This is just a helper function for now
    void printLoopVector(std::vector<BasicBlock*> loop_vector)
    {

    	 // debug printing
    	for (unsigned int i = 0; i < loop_vector.size(); i++)
		{
			BasicBlock* loopitem = loop_vector[i];
			loopitem->printAsOperand(errs(), false);
			errs() << ",";
		}

    }

    // This algorithm follows the algorithm provided by the powerpoint slides
    void loopAlgorithm(std::vector<std::pair<BasicBlock*, BasicBlock*>> &backedge_vector, std::vector<BasicBlock*> &loop_vector, int backedge_count)
    {
		// create an empty stack
		std::stack <BasicBlock*> stack;

		// remember pair is <N,D>
		// insert D into loop vector
		loop_vector.push_back(backedge_vector[backedge_count].first);
		
		// insert n onto stack
		stack.push(backedge_vector[backedge_count].second);
		BasicBlock * original_sink = backedge_vector[backedge_count].second;

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
				//errs() << "predecessor BB:  ";
				//predecessor->printAsOperand(errs(), false);
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
	} // END of loopAlgorithm

	// This code finds the back edges
	void findBackEdges(Function &func, DominatorTree &domtree, std::pair <BasicBlock*, BasicBlock*> &backedge_pair, std::vector<std::pair<BasicBlock*, BasicBlock*>> &backedge_vector, int &bbNum, int &backedge_count)
	{
		bool dom;
		
		// Loops through basic blocks
		for (Function::iterator bb = func.begin(), e=func.end(); bb != e; ++bb)
		{
			errs() << "BasicBlock " << bbNum <<"\n";
			bb->printAsOperand(errs(), false);
			bb->dump();
			bbNum += 1;
			
			//errs() << "Num of successors: " << bb->getTerminator()->getNumSuccessors() <<"\n";
			
			// Loops through each successor
			 for (unsigned int i = 0; i < bb->getTerminator()->getNumSuccessors(); i++)
			 {

			 	//errs() << "Succ:" << bb->getTerminator()->getSuccessor(i) <<"\n";
			 	dom = domtree.dominates(bb->getTerminator()->getSuccessor(i)->getTerminator(), bb->getFirstInsertionPt());
			 	//errs () << "bool result: " << dom << "\n";
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

	}// END of findBackEdges

	// This code finds the innermost loop
	void findInnermostLoop(std::vector<std::pair<BasicBlock*, BasicBlock*>> &backedge_vector, std::vector<BasicBlock*> &loop_vector,std::vector<std::vector<BasicBlock*>> &innerloop_vector)
	{
		int temp_backedge_count = 0;
		BasicBlock* backedge_bb_1;
		BasicBlock* backedge_bb_2;

		errs() << "Innermost Loops:\n";
		for (unsigned int i = 0; i < loop_vector.size(); i++)
		{
			BasicBlock* loop_bb = loop_vector[i];

			//check if found basic block in loop exists as a backedge vector
			for  (unsigned int j = 0; j < backedge_vector.size(); j++)
			{
				backedge_bb_1  = backedge_vector[j].first;
				backedge_bb_2  = backedge_vector[j].second;
				// must match the backedge pair
				if(backedge_bb_1 == loop_bb || backedge_bb_2 == loop_bb)
				{
					temp_backedge_count += 1;
				}
			}
		}
		// this is 2 because it must match back edge pair
		if (temp_backedge_count <= 2)
		{
			//errs() << "Innermost loop found!" << "\n";
			innerloop_vector.push_back(loop_vector);

			
			// debugging print statements
			errs() << "{";
			for (unsigned int i = 0; i < innerloop_vector.size(); i++)
			{
				errs() << "(";
				for (unsigned int j = 0; j < innerloop_vector[i].size(); j++)
				{
					BasicBlock* loopitem = innerloop_vector[i][j];
					loopitem->printAsOperand(errs(), false);
					if (j != innerloop_vector[i].size()-1)
					{
						errs() << ",";
					}
				}
				errs() << ")";

				if (i != innerloop_vector.size()-1)
				{
					errs() << ",";
				}

			}
			errs() << "}";
			
		}
		errs() << "\n";

	}

    bool doInitialization(Module &M) override 
    {
		std::stack <BasicBlock*> stack;
		std::pair <BasicBlock*, BasicBlock*> backedge_pair;
		std::vector<std::pair<BasicBlock*, BasicBlock*>> backedge_vector; 
     	errs() << "Module: " << M.getName() << "\n";
		errs() << "\n---------Starting BasicBlockDemo---------\n";
		//////////// LOOP ALGORITHM START ///////////////////
		// Loops through functions
		for (Module::iterator func = M.begin(), y = M.end(); func != y; ++func)
		{ 
			std::vector<std::vector<BasicBlock*>> innerloop_vector;
			std::vector<BasicBlock*> loop_vector;
			
			errs() << "\n---------Start of function ---------\n";
			int bbNum = 0;
			int backedge_count = 0;
			int tot_backedge = 0;
			errs() << "Function: " << func->getName() <<"\n"; // print out function numbers
			
			// First draw dominator tree
			DominatorTree domtree;
			
			// hacked this from this source because the printf was giving me a segfault
			// https://stackoverflow.com/questions/23929468/identifying-user-define-function-through-llvm-pass
			if(func->size()>0)
			{
				domtree.recalculate(*func);
			}
			findBackEdges(*func, domtree, backedge_pair, backedge_vector, bbNum, backedge_count);
			tot_backedge = backedge_count;
			//errs() << "BACK EDGES count: " << backedge_count << "\n";
			///////////////// Loop Algorithm from slides ///////////////////////////
			// loop through backedge list
			while(backedge_count--)
			{
				std::vector<BasicBlock*> loop_vector; 
				loopAlgorithm(backedge_vector, loop_vector, backedge_count);
				
				// Now check to see if the loop found is the innermost loop
				// if of the loop block items found, if it contains another back edge, toss it because it's not the inner one
				// for each item in loop vector
				findInnermostLoop(backedge_vector, loop_vector, innerloop_vector);
			} // end of backedge list
		if (tot_backedge > 0)
		{
			topologicalOrdering(innerloop_vector);
			findEdgeProfiling(topo_loop_vector);
			//std::vector<std::vector<BasicBlock*>>(innerloop_vector).swap(innerloop_vector);
			//std::vector <BasicBlock*>(loop_vector).swap(loop_vector);
		}
		else
		{
			errs() << "Edge values:\n";
			errs() << "{ }";
		}
		//////////// EDGE LABEL END /////////////////////////////
		errs() << "\n";
		errs() << "//////////// FUNCTION END ///////////////\n\n";
		//std::vector<std::pair<BasicBlock*, BasicBlock*>>(innerloop_vector).swap(innerloop_vector);
	}// end of function loop 
	

	//////////// EDGE START /////////////////////////////

	Context = &M.getContext();
  	printf_func = printf_prototype(*Context, &M);
  	errs() << "\nModule: " << M.getName() << "\n";

  	//here doInitialization for the name of the blocks
  	for(auto &F:M)
  	{
  		int i = 0;
  		for(auto &bb:F)
  		{
  	  		if(!bb.hasName())
  	    		{
  					bb.setName("b" + to_string(i));
  				}
  			i++;
  		}
  	
  		int numberofbasicBlock = i;
  		//we should create a link between a edgeCounter and context and then in runonbasicblock we should change this edgeCounters variable.
  	
 
  	// Global Variable Declarations

  	 //https://stackoverflow.com/questions/23330018/llvm-global-integer-array-zeroinitializer
	// Type Definitions
	// ArrayType* ArrayTy_0 = ArrayType::get(IntegerType::get(mod->getContext(), 32), 5);
	// // Function Declarations
	// // Global Variable Declarations
	// GlobalVariable* gvar_array_a = new GlobalVariable(/*Module=*/*mod, 
	// /*Type=*/ArrayTy_0,
	// /*isConstant=*/false,
	// /*Linkage=*/GlobalValue::ExternalLinkage,
	// /*Initializer=*/0, // has initializer, specified below
	// /*Name=*/"a");
	// gvar_array_a->setAlignment(16);
	// // Constant Definitions
	// ConstantAggregateZero* const_array_2 = ConstantAggregateZero::get(ArrayTy_0);

	// // Global Variable Definitions
	// gvar_array_a->setInitializer(const_array_2);

        ArrayType* ArrayTy_0 = ArrayType::get(ArrayType::get(IntegerType::get(M.getContext(), 32), numberofbasicBlock), numberofbasicBlock);
        GlobalVariable* gVariable = new GlobalVariable(M, ArrayTy_0, false, GlobalValue::ExternalLinkage, 0, "edgeCounter");
        ConstantAggregateZero* initValues = ConstantAggregateZero::get(ArrayTy_0);
        gVariable->setInitializer(initValues);
        edgeCounter[F.getName()] = gVariable;

    }

    //bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
    //previousBlockID should be defined like bbCounter
    previousBlockID = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "previousBlockID");
    bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	
	int totalNumPaths;
	for (unsigned l = 0; l < totNumPath.size(); l++)
	{
		totalNumPaths = totNumPath[l];
	}
	errs() << "TOTAL PATHS:" << totalNumPaths << "\n";

	//////// NEED TO UPDATE THIS
	// The following creates a global array
	ArrayType* arrayType = ArrayType::get(Type::getInt32Ty(*Context),totalNumPaths);
	pathCounter = new GlobalVariable(M,arrayType,false,GlobalValue::ExternalLinkage,Constant::getNullValue(arrayType),"pathCounter");

	const char *finalPrintString = "BB Count: %d\n";
	Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	printf_func = printf_prototype(*Context, &M);
 	   

    //////////// EDGE END /////////////////////////////

    return true;
    }
    //----------------------------------
    bool doFinalization(Module &M) 
    {
      // errs() << "-------Finished BasicBlocksDemo----------\n";
 
      return false;
    }
    
    //----------------------------------

    bool runOnFunction(Function &F) override 
    {
    	

		//	blocks,predecessors,edges,block_ids
 	  	//in each function we need to define the string of blocks that exist in each function
 	  	set<string> blocks;//b0,b1,..

 	  	//for each block we should define predecessors of each block
 	  	map<string,set<string>> predecessors;

 	  	//we should define edges as a pair of two basic blocks(terminator and entry)
 	  	set<pair<string,string>> edges;	

 	  	//we define blocknum as a map from the string name of the block to the block number b0 -> 0
 	  	map<string,int> blocknum;
     	errs() << "Function: " << F.getName() << '\n';

 	  	int i = 0;

 	  	for(auto &bb:F)
 	  	{
 	  		blocks.insert(bb.getName());
 	  		blocknum[bb.getName()] = i;
 	  		i++;
 	  	}
 	  	FuncNameToBlockNumber[F.getName()]= blocknum;

 	  	//predecessors:
 	  	for(auto &bb:F)
 	  	{
 	  		//TerminatorInst Class Reference : Subclasses of this class are all able to terminate a basic block
        	TerminatorInst *TI = bb.getTerminator();
        	for(unsigned s = 0, e = TI->getNumSuccessors(); s!= e; s++)
        	{
         		string bbname = TI->getSuccessor(s)->getName();//b0->b1 then bbname is b1
          
          		set<string> predecss;
          		predecss.insert(bb.getName());
          		predecessors[bbname] = predecss;

          		edges.insert(make_pair(bb.getName(),bbname));
			}
 	  	}
 		FuncNameToEdges[F.getName()] = edges;

		errs() << "\n";
		errs() << "//////////// FUNCTION END ///////////////\n\n";
		//std::vector<std::pair<BasicBlock*, BasicBlock*>>(innerloop_vector).swap(innerloop_vector);


 		//$$$$$$$$///////////////////////////////////////////////////////////////////////////////////////////////////
		// Initialize a global array of counts
		//done as pathCounter

		// Insert instrumentation code in the top of the loop's BB to initialize a global BBCounter = 0.
		


		/*addBBCounterToTop(topo_loop_vector);
		insertBB(EdgeValueMap,F);


		//insertBBEnd(topo_loop_vector);
		addPathCounterToEnd(topo_loop_vector);
		addBBCounterToEnd(topo_loop_vector);// this resets the BBcounter back to 0
*/
		// Insert instrumentation BB in every edge that contains a BBCounter and the weight to add to BBCounter.
				

		//Insert instrumentation code at the end of the loop to index BBCounter in the global array of counts.
 		
 		////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			
		errs() << "\n";
 		for(auto &BB: F) 
 		{
        	BB.printAsOperand(errs(), false);
    	}
    	errs() << "\n";

    	//for each item in loop, go from top to end, finding 
    	if(!(F.getName().equals("main")))
    	{
    		temp(topo_loop_vector, EdgeValueMap, F);
    	}
    	

 		for(auto &BB: F) 
 		{

        //  statement BEFORE calling runOnBasicBlock
        	if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator()))
        	{ // major hack?
          		//addFinalPrintf_edge(BB);
          		//addFinalPrintf(BB, Context, bbCounter, BasicBlockPrintfFormatStr, printf_func);
          		addFinalPrintf_paths(BB, Context, pathCounter,printf_func);

        	}
        	//runOnBasicBlock(BB);
        	
        	
    	}
 

      return true; // since runOnBasicBlock has modified the program
    }
     //-------------------------

    void temp (std::vector<std::vector<BasicBlock*>> &topo_loop_vector, std::map<std::pair<BasicBlock*,BasicBlock*>,int> &EdgeValueMap, Function &F)
    {

		addBBCounterToTop(topo_loop_vector);
		insertBB(EdgeValueMap,F);
		addPathCounterToEnd(topo_loop_vector);
		addBBCounterToEnd(topo_loop_vector);// this resets the BBcounter back to 0
    }

	void insertBBEnd(std::vector<std::vector<BasicBlock*>> &innerloop_vector)
	{
			int i = 0;
			int end = topo_loop_vector[i].size()-1;



			BasicBlock* bb1 = topo_loop_vector[i][0];
			BasicBlock* bb2 = topo_loop_vector[i][end];


			errs() << "\nnew temp\n";
			bb1->printAsOperand(errs(), false);
			bb1->getTerminator()->getSuccessor(0)->printAsOperand(errs(), false);

	    	BasicBlock* temp = llvm::BasicBlock::Create(*Context,"",bb2->getParent() ,bb2);
			//bb2->removePredecessor(bb1, true);
			bb1->getTerminator()->setSuccessor(0,temp);
			errs() << "\nafter removal...\n";
			bb1->getTerminator()->getSuccessor(0)->printAsOperand(errs(), false);
			errs() << "\nOutput...\n";
			bb1->printAsOperand(errs(), false);
			errs() << "\n";
			bb2->printAsOperand(errs(), false);
			errs() << "\n";
			temp->printAsOperand(errs(), false);
			errs() << "\n";

			IRBuilder<> IRB(temp); // Will insert the generated instructions BEFORE the first BB instruction	 
			Value *loadAddr = IRB.CreateLoad(bbCounter);
			Value *addAddr = IRB.CreateAdd(loadAddr, ConstantInt::get(Type::getInt32Ty(*Context), 1));
			IRB.CreateStore(addAddr, bbCounter);

			IRB.CreateBr(bb2); // sets new basic block to point to bb2



	}


	void addPathCounterToEnd(std::vector<std::vector<BasicBlock*>> &topo_loop_vector)
	{
	   // for (unsigned i = 0, e = innerloop_vector.size(); i != e; ++i)
	    //{
		unsigned i = 0;
		for (unsigned x = 0; x < topo_loop_vector[i].size(); x++)
		{
			errs()<<"!\n";
			topo_loop_vector[0][x]->printAsOperand(errs(), false);
		}


			int tempSize = topo_loop_vector[i].size()-1;
	    	errs() << "\n";
	    	errs() << "end added:\n";
	    	topo_loop_vector[i][0]->printAsOperand(errs(), false);
	    	errs() << "\n";
	    	errs() << "\n";
	    	errs() << "beginning branch added:\n";
	    	topo_loop_vector[i][tempSize]->printAsOperand(errs(), false);
			BasicBlock* endBB = topo_loop_vector[i][0];
			IRBuilder<> IRB(endBB->getFirstInsertionPt());
			


			Value* loadAddr = IRB.CreateLoad(bbCounter);
			//Value* new_val;
			//new_val->replaceAllUsesWith(loadAddr);

			
			//IRB.CreateBr(topo_loop_vector[i][tempSize]);
/*
			LoadInst* loadArea = new LoadInst(loadAddr, "", false, endBB->getTerminator());



			ConstantInt* const_int64_6 = ConstantInt::get(*Context, APInt(64, StringRef("0"), 10));

			std::vector<Value*> gepIndices(1);
			gepIndices[0] = const_int64_6;

			BinaryOperator* int32_8 = BinaryOperator::Create(Instruction::Add, loadAddr, const_int64_6, "add", endBB->getTerminator());
			Value* idxValue = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context),0),loadAddr);




			CastInst* int64_idxprom = new SExtInst(idxValue, IntegerType::get(*Context, 64), "idxprom", endBB->getTerminator()); // you need to define int32_8 as type of BinaryOperator* with creating a Add instruction for your edge value to be added
			 
			std::vector<Value*> ptr_arrayidx_indices;
			ptr_arrayidx_indices.push_back(const_int64_6);
			ptr_arrayidx_indices.push_back(int64_idxprom);
			 
			Instruction* ptr_arrayidx = GetElementPtrInst::Create(pathCounter, ptr_arrayidx_indices, "arrayidx", endBB->getTerminator());
*/

			Value* idxValue = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context),0),loadAddr);
			ConstantInt* initvalue = ConstantInt::get(*Context, APInt(32, StringRef("0"), 10));
			std::vector<Value*> gepIndices(2);
			gepIndices[0] = initvalue;
			gepIndices[1] = loadAddr;

			GetElementPtrInst* pcpointer = GetElementPtrInst::Create(pathCounter,gepIndices,"pcptr",endBB->getTerminator());
			LoadInst* oldpc = new LoadInst(pcpointer,"oldpc",endBB->getTerminator());
			Value* newpc = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context),1),oldpc);
			new StoreInst(newpc,pcpointer,endBB->getTerminator());


			//Value *loadAddr_2 = IRB.CreateLoad(bbCounter);
			Value *addAddr_1 = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 0),ConstantInt::get(Type::getInt32Ty(*Context), 0));
			IRB.CreateStore(addAddr_1, bbCounter);
			errs() << "\n";
 


			//IRB.CreateBr(innerloop_vector[i][0]); // sets new basic block to point to bb2


	   // }
	}

	void addBBCounterToEnd(std::vector<std::vector<BasicBlock*>> &innerloop_vector)
	{
	    for (unsigned i = 0, e = innerloop_vector.size(); i != e; ++i)
	    {
	    	errs() << "\n";
	    	innerloop_vector[i][0]->printAsOperand(errs(), false);
			IRBuilder<> IRB(innerloop_vector[i][0]->getTerminator());
			//Value *loadAddr = IRB.CreateLoad(bbCounter);
			Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 0),ConstantInt::get(Type::getInt32Ty(*Context), 0));
			IRB.CreateStore(addAddr, bbCounter);
			errs() << "\n";
	    }
	}

	void insertBB(std::map<std::pair<BasicBlock*,BasicBlock*>,int> &EdgeValueMap, Function &F)
	{

		for(std::map<std::pair<BasicBlock*, BasicBlock*>,int>::iterator iter = EdgeValueMap.begin(); iter != EdgeValueMap.end(); ++iter)
		{
			BasicBlock* bb1 = iter->first.first;
			BasicBlock* bb2 = iter->first.second;

			//std::pair<BasicBlock*,BasicBlock*> edgeBBPair;
			//edgeBBPair = make_pair(bb1, bb2);
			int edge = iter->second;

			

			errs() << "\nnew temp\n";
			
			for (unsigned i = 0, e = bb1->getTerminator()->getNumSuccessors(); i != e; ++i)
			{
				errs() << "\nFound successors...\n";
				bb1->getTerminator()->getSuccessor(i)->printAsOperand(errs(), false);

			    if (bb1->getTerminator()->getSuccessor(i) == bb2) 
			    {
			    	BasicBlock* temp = llvm::BasicBlock::Create(*Context,"",bb2->getParent() ,bb2);
					//bb2->removePredecessor(bb1, true);
					bb1->getTerminator()->setSuccessor(i,temp);
					errs() << "\nafter removal...\n";
					bb1->getTerminator()->getSuccessor(i)->printAsOperand(errs(), false);
					errs() << "\nOutput...\n";
					bb1->printAsOperand(errs(), false);
					errs() << "\n";
					bb2->printAsOperand(errs(), false);
					errs() << "\n";
					temp->printAsOperand(errs(), false);
					errs() << "\n";

					IRBuilder<> IRB(temp); // Will insert the generated instructions BEFORE the first BB instruction	 
					Value *loadAddr = IRB.CreateLoad(bbCounter);
					Value *addAddr = IRB.CreateAdd(loadAddr, ConstantInt::get(Type::getInt32Ty(*Context), edge));
					IRB.CreateStore(addAddr, bbCounter);
					IRB.CreateBr(bb2); // sets new basic block to point to bb2


			    }

			}


			
		}
	}


	void addBBCounterToTop(std::vector<std::vector<BasicBlock*>> &innerloop_vector)
	{
		errs() << "bbcounter added to block as 0: \n";
	    for (unsigned i = 0, e = innerloop_vector.size(); i != e; ++i)
	    {
	    	//int tempSize = innerloop_vector[i].size()-1;
	    	errs() << "\n";
	    	//innerloop_vector[i][tempSize]->printAsOperand(errs(), false);

	    	for (unsigned int i = 0; i < innerloop_vector.size(); i++)
			{
				
				// This loops through nested innerloop vecotr
				for (unsigned int j = 1; j < innerloop_vector[i].size(); j++)
				{
					if(j == innerloop_vector[i].size()-1)
					{
						BasicBlock* firstBB;
						firstBB = innerloop_vector[i][j];
						IRBuilder<> IRB(firstBB->getFirstInsertionPt());
						Value *loadAddr = IRB.CreateLoad(bbCounter);

						Value *addAddr = IRB.CreateAdd(loadAddr, ConstantInt::get(Type::getInt32Ty(*Context), 0));
						IRB.CreateStore(addAddr, bbCounter);

					}
				} // end nested innerloop vector
			} // end innerloop vector



			errs() << "\n";
	    }
	}


    bool runOnBasicBlock(BasicBlock &BB) 
    {
 
      // Value *loadAddr = IRB.CreateLoad(bbCounter);
      // Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
      // IRB.CreateStore(addAddr, bbCounter);
 
      // for(auto &I: BB)
      //   errs() << I << "\n";

    	//something here not done yet
    	// errs() << "BasicBlock: " << BB.getName() << '\n';
    	IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
    	// //this is a place for globalvariable that we definded in the first part of program
    	// //previousBlockID, edgeCounter we need two index for two basic block b0->b1
    	// //to create edgeCounter we need edge indexes


      Value* zeroIndex = Constant::getNullValue(IntegerType::getInt32Ty(*Context));//everything is in the class fo value

      std::vector<Value*> edgeIndex;
      edgeIndex.push_back(zeroIndex);

       // for(std::vector<Value*>::iterator it = edgeIndex.begin();it!=edgeIndex.end();it++)
       //  errs()<<*it<<"kdkdjkdjkd"<<"\n";

      Value* indexFirst = IRB.CreateLoad(previousBlockID);

      edgeIndex.push_back(indexFirst);
      Value* indexSecond = ConstantInt::get(Type::getInt32Ty(*Context), FuncNameToBlockNumber[BB.getParent()->getName()][BB.getName()]);
    
     
      edgeIndex.push_back(indexSecond);

	        

      Value* edgeCountVal = IRB.CreateGEP(edgeCounter[BB.getParent()->getName()], edgeIndex);
      Value* OldEdgeCountVal = IRB.CreateLoad(edgeCountVal);
      Value *edgeAddCounter = IRB.CreateAdd(OldEdgeCountVal, ConstantInt::get(Type::getInt32Ty(*Context), 1));
      IRB.CreateStore(edgeAddCounter, edgeCountVal);

      IRBuilder<> builder(BB.getTerminator());
      Value *blockID = ConstantInt::get(Type::getInt32Ty(*Context), FuncNameToBlockNumber[BB.getParent()->getName()][BB.getName()]);
      

      builder.CreateStore(blockID, previousBlockID);
 
      return true;
    }
    
    void addFinalPrintf_edge(BasicBlock& BB)
    {
    	// map<string,GlobalVariable*> edgeCounter;  
    	// edgeCounter is a map from the function name(string) to the address(string)
    	for(auto &function: edgeCounter)
    	{
    		printEdgeCount(BB, function.first, FuncNameToEdges[function.first], function.second);

      	}
    }

     void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, GlobalVariable *bbCounter, GlobalVariable *var, Function *printf_func) 
     {
     	errs() << "Printing final blocks output\n";
		IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
		std::vector<Constant*> indices;
		Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
		indices.push_back(zero);
		indices.push_back(zero);
		Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);

		Value *bbc = builder.CreateLoad(bbCounter);
		CallInst *call = builder.CreateCall2(printf_func, var_ref, bbc);
		call->setTailCall(false);
    }

     void addFinalPrintf_paths(BasicBlock& BB, LLVMContext *Context, GlobalVariable *pathCounter, Function *printf_func) 
     {
     	IRBuilder<> IRB(BB.getTerminator());

	    std::string a;
	    a =  a + ": %d\n";
	    const char *finalPrintString = a.c_str();
	    Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	    BasicBlockPrintfFormatStr = new GlobalVariable(*((BB.getParent())->getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), 
							   true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");

	    //printf_func = printf_prototype(*Context, ((BB.getParent())->getParent()));

	    Value* idxValue = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context),0),ConstantInt::get(Type::getInt32Ty(*Context),0));
	    std::vector<Value*> gepIndices(2);
	    ConstantInt* initvalue = ConstantInt::get(*Context, APInt(32, StringRef("0"), 10));
	    gepIndices[0] = initvalue;
	    gepIndices[1] = idxValue;
	    GetElementPtrInst* pcpointer = GetElementPtrInst::Create(pathCounter,gepIndices,"pcptr",BB.getTerminator());
	    //load from array
	    LoadInst* oldpc = new LoadInst(pcpointer,"oldpc",BB.getTerminator());

	    std::vector<Constant*> indices;
	    Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
	    indices.push_back(zero);
	    indices.push_back(zero);
	    Constant *var_ref = ConstantExpr::getGetElementPtr(BasicBlockPrintfFormatStr, indices);
	    CallInst *call = IRB.CreateCall2(printf_func, var_ref, oldpc);
    	call->setTailCall(false);



    }

    Function* printf_prototype(LLVMContext& ctx, Module *mod) {
	std::vector<Type*> printf_arg_types;
	printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
		 
	FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
	Function *func = mod->getFunction("printf");
	if(!func)
	    func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
	func->setCallingConv(CallingConv::C);
	return func;
    }


    void printEdgeCount(BasicBlock& BB, string funcName, set<pair<string, string>> edges, GlobalVariable* counter) {



      	int i = 0;
      	IRBuilder<> builder(BB.getTerminator());

      	for(auto &edge: edges) {
        

	      	const char *finalPrintString =  (edge.first + "->" + edge.second + ": %d\n").c_str();
	        Constant *edgelink = ConstantDataArray::getString(*Context, finalPrintString);

	     //BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
      	// printf_func = printf_prototype(*Context, &M);

	        GlobalVariable *var;
	        var = new GlobalVariable(*(BB.getParent()->getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, edgelink, "EdgePrintStr");
	     

	        std::vector<Constant*> indices;
	        Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
	        indices.push_back(zero);
	        indices.push_back(zero);
	        Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);


	        
	        Constant *zeroIndex = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
	        std::vector<Constant*> edgeIndex;
	        edgeIndex.push_back(zeroIndex);

	        ConstantInt* indexFirst = ConstantInt::get(Type::getInt32Ty(*Context), FuncNameToBlockNumber[funcName][edge.first]);
	        edgeIndex.push_back(indexFirst);

	        ConstantInt* indexSecond = ConstantInt::get(Type::getInt32Ty(*Context), FuncNameToBlockNumber[funcName][edge.second]);
	        edgeIndex.push_back(indexSecond);

	        Constant* edgeCountVal = ConstantExpr::getGetElementPtr(counter, edgeIndex);

	        Value *edgeCount = builder.CreateLoad(edgeCountVal);
	        CallInst *call = builder.CreateCall2(printf_func, var_ref, edgeCount);
	        call->setTailCall(false);
	        i++;
      }
    }
 
};
}
    

char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);