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

    // llvm global variables
    GlobalVariable *bbCounter = NULL;
    GlobalVariable *previousBlockID = NULL;
    GlobalVariable *BasicBlockPrintfFormatStr = NULL;
    GlobalVariable *pathCounter = NULL;
    GlobalVariable *pathCounterSingle = NULL;

    // static global variables
    int totalNumPaths;

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

    // This function finds the edge weights as per the Ball-Larus algorithm in "Efficient path profiling"
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
					 		
					 		//successorBB->printAsOperand(errs(), false);
					 		NumPathsMap[currentBB] = NumPathsMap[currentBB] + NumPathsMap[successorBB];
					 		//errs() << EdgeValueMap<currentBB, successorBB>;
				 		}

				 	}

				}

				if (j >= (topo_loop_vector[i].size() - 1))
				{
					totNumPath.push_back(NumPathsMap[currentBB]);
				}
			} // end nested innerloop vector
		} // end innerloop vector

		// following prints the output for the edge values
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
    }// END of findEdgeProfiling

    // This function finds the topological ordering of the loop vector
    void topologicalOrdering(std::vector<std::vector<BasicBlock*>> innerloop_vector)
    {
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
			} // end nested innerloop vector
			temp_vector.push_back(innerloop_vector[i][0]);
			topo_loop_vector.push_back(temp_vector);
		} // end innerloop vector

    } // END of topologicalOrdering

    // This algorithm follows the algorithm provided by the powerpoint slides
    // http://www.cs.ucr.edu/~gupta/teaching/201-18/schedule18.html
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

				// if not in loop vector, insert pred into stack
				// referred to this https://stackoverflow.com/questions/571394/how-to-find-out-if-an-item-is-present-in-a-stdvector
				if (std::find(loop_vector.begin(), loop_vector.end(), predecessor) != loop_vector.end() )
				{
					// do nothing
				}	
				else if (predecessor != original_sink) // make sure also pred != original sink
				{
					loop_vector.push_back(predecessor);
					stack.push(predecessor);
				}
				else
				{
					loop_vector.push_back(predecessor);
				}
				
			}
		}
	} // END of loopAlgorithm

	// This code finds the back edges by using the dominator tree
	void findBackEdges(Function &func, DominatorTree &domtree, std::pair <BasicBlock*, BasicBlock*> &backedge_pair, std::vector<std::pair<BasicBlock*, BasicBlock*>> &backedge_vector, int &bbNum, int &backedge_count)
	{
		bool dom;
		
		// Loops through basic blocks
		for (Function::iterator bb = func.begin(), e=func.end(); bb != e; ++bb)
		{
			errs() << "BasicBlock:b" << bbNum << ", Label: ";
			bb->printAsOperand(errs(), false);
			errs() << "\n";

			bb->dump();
			bbNum += 1;
			
			// Loops through each successor
			 for (unsigned int i = 0; i < bb->getTerminator()->getNumSuccessors(); i++)
			 {

			 	//errs() << "Succ:" << bb->getTerminator()->getSuccessor(i) <<"\n";
			 	dom = domtree.dominates(bb->getTerminator()->getSuccessor(i)->getTerminator(), bb->getFirstInsertionPt());
			 	//errs () << "bool result: " << dom << "\n";
			 	if (dom && (bb->getTerminator()->getNumSuccessors() > 0)) // is a back edge
			 	{

			 		// now add back edge onto list of backedges
			 		// pair is <N, D>
					backedge_pair = std::make_pair(bb->getTerminator()->getSuccessor(i),bb); 

					backedge_vector.push_back(backedge_pair);
					backedge_count += 1;
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

		}

	}

	// this is run before the function is run
    bool doInitialization(Module &M) override 
    {
		std::stack <BasicBlock*> stack;
		std::pair <BasicBlock*, BasicBlock*> backedge_pair;
		std::vector<std::pair<BasicBlock*, BasicBlock*>> backedge_vector; 
     	errs() << "Module: " << M.getName() << "\n";

     	/////////////////////////////////////////////////////////////
     	// The following section figures out the innermost loops/////
     	/////////////////////////////////////////////////////////////

		// Loops through functions
		for (Module::iterator func = M.begin(), y = M.end(); func != y; ++func)
		{ 
			std::vector<std::vector<BasicBlock*>> innerloop_vector;
			std::vector<BasicBlock*> loop_vector;
			int bbNum = 0;
			int backedge_count = 0;
			int tot_backedge = 0;

			errs() << "Function: " << func->getName() <<"\n"; // print out function numbers
			
			// First draw dominator tree
			DominatorTree domtree;
			
			// Got help from this source because the printf was giving me a segfault
			// https://stackoverflow.com/questions/23929468/identifying-user-define-function-through-llvm-pass
			if(func->size()>0)
			{
				domtree.recalculate(*func);
			}
			findBackEdges(*func, domtree, backedge_pair, backedge_vector, bbNum, backedge_count);

			tot_backedge = backedge_count;

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

			// output print for innermost loops
			errs() << "Innermost Loops:\n";
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
			errs() << "}\n";

			// prints out edge values
			if (tot_backedge > 0)
			{
				topologicalOrdering(innerloop_vector);
				findEdgeProfiling(topo_loop_vector);
			}
			else
			{
				errs() << "Edge values:\n";
				errs() << "{}";
			}
			errs() << "\n";
		}// end of function loop 

     	/////////////////////////////////////////////////////////////
     	// The following section is used to set up edge profiling////
     	/////////////////////////////////////////////////////////////

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

		previousBlockID = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "previousBlockID");
		bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");

		for (unsigned l = 0; l < totNumPath.size(); l++)
		{
			totalNumPaths = totNumPath[l];
		}
		//errs() << "TOTAL PATHS:" << totalNumPaths << "\n";

		if (totalNumPaths > 1)
		{
			// The following creates a global array
			ArrayType* arrayType = ArrayType::get(Type::getInt32Ty(*Context),totalNumPaths);
			pathCounter = new GlobalVariable(M,arrayType,false,GlobalValue::ExternalLinkage,Constant::getNullValue(arrayType),"pathCounter");
		}
		else
		{
			pathCounterSingle = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "pathCounterSingle");
		}

		const char *finalPrintString = "BB Count: %d\n";
		Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
		BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
		printf_func = printf_prototype(*Context, &M);


    return true;

    }

    //----------------------------------
    bool doFinalization(Module &M) 
    {
 
      return false;
    }
    
    //----------------------------------
    // the following is run for every function during run time for dynamic analysis
    bool runOnFunction(Function &F) override 
    {
    	/////////////////////////////////////////////////////////////
     	// The following section is for edge profiling///////////////
     	/////////////////////////////////////////////////////////////
    	
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

    	/////////////////////////////////////////////////////////////
     	// The following section is for path profiling///////////////
     	/////////////////////////////////////////////////////////////

    	if(!(F.getName().equals("main")))
    	{
    		pathProfiling(topo_loop_vector, EdgeValueMap, F);
    	}
    	
    	/////////////////////////////////////////////////////////////
     	// The following section is for the output //////////////////
     	/////////////////////////////////////////////////////////////

    	errs() << "Output of profiled program:\n\n"; 
 		for(auto &BB: F) 
 		{
        //  statement BEFORE calling runOnBasicBlock
        	if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator()))
        	{
        		addFinalPrintfEdge(BB);
          		
          		if (totalNumPaths > 1)
          		{
          			addFinalPrintfPaths(BB, Context, pathCounter, printf_func);
          		}
          		else
          		{
          			addFinalPrintfPaths(BB, Context, pathCounterSingle, printf_func);
          		}

        	}
        	runOnBasicBlock(BB);
    	}
      return true; // since runOnBasicBlock has modified the program
    }
     //-------------------------

    // this is a wrapper function that calls all the necessary functions in order to insert the instrumentation code
    void pathProfiling (std::vector<std::vector<BasicBlock*>> &topo_loop_vector, std::map<std::pair<BasicBlock*,BasicBlock*>,int> &EdgeValueMap, Function &F)
    {
    	//for (unsigned int j = 0; j < topo_loop_vector.size(); j++)
		//{
			unsigned int j = 0;
			addBBCounterToTop(topo_loop_vector[j]);

			if (j==0)
			{
				insertBB(EdgeValueMap,F);
			}

			if (totalNumPaths > 1)
			{
				addPathCounterToEndArray(topo_loop_vector[j]);
				addBBCounterToEnd(topo_loop_vector[j]);// this resets the BBcounter back to 0
			}
			else
			{
				addPathCounterToEndSingle(topo_loop_vector[j]);
				addBBCounterToEnd(topo_loop_vector[j]);// this resets the BBcounter back to 0
			}
			
				
		//}
    }

    // this function adds the global array to the last block of the innermost loop
    // it then uses the local sum (bbCounter) in order to figure out where to index in the global array
	void addPathCounterToEndArray(std::vector<BasicBlock*> &topo_loop_vector_nested)
	{
			BasicBlock* endBB = topo_loop_vector_nested[0];
			IRBuilder<> IRB(endBB->getFirstInsertionPt());
			std::vector<Value*> ptr_arrayidx_indices;
			ConstantInt* const_int64_6 = ConstantInt::get(*Context, APInt(64, StringRef("0"), 10));
			Value* loadAddr = IRB.CreateLoad(bbCounter);
			ptr_arrayidx_indices.push_back(const_int64_6);
			ptr_arrayidx_indices.push_back(loadAddr);
			Instruction* ptr_arrayidx = GetElementPtrInst::Create(pathCounter, ptr_arrayidx_indices, "arrayidx", endBB->getTerminator());
			LoadInst* arrayLoadInstruction = new LoadInst(ptr_arrayidx,"loadAddr",false,endBB->getTerminator());
			Value* updatedValue = IRB.CreateAdd(arrayLoadInstruction,ConstantInt::get(Type::getInt32Ty(*Context),1));
			new StoreInst(updatedValue,ptr_arrayidx,endBB->getTerminator());
	}

	void addPathCounterToEndSingle(std::vector<BasicBlock*> &topo_loop_vector_nested)
	{
		IRBuilder<> IRB(topo_loop_vector_nested[0]->getTerminator());
		Value *loadAddr = IRB.CreateLoad(pathCounterSingle);
		Value *addAddr = IRB.CreateAdd(loadAddr, ConstantInt::get(Type::getInt32Ty(*Context), 1));
		IRB.CreateStore(addAddr, pathCounterSingle);
	}

	void addBBCounterToEnd(std::vector<BasicBlock*> &topo_loop_vector_nested)
	{
		IRBuilder<> IRB(topo_loop_vector_nested[0]->getTerminator());
		Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 0),ConstantInt::get(Type::getInt32Ty(*Context), 0));
		IRB.CreateStore(addAddr, bbCounter);
	}

	void insertBB(std::map<std::pair<BasicBlock*,BasicBlock*>,int> &EdgeValueMap, Function &F)
	{
		for(std::map<std::pair<BasicBlock*, BasicBlock*>,int>::iterator iter = EdgeValueMap.begin(); iter != EdgeValueMap.end(); ++iter)
		{
			int edge = iter->second;
			BasicBlock* bb1 = iter->first.first;
			BasicBlock* bb2 = iter->first.second;
			
			for (unsigned int j = 0; j < bb1->getTerminator()->getNumSuccessors(); j++)
			{
			    if (bb1->getTerminator()->getSuccessor(j) == bb2) 
			    {
			    	BasicBlock* temp = llvm::BasicBlock::Create(*Context,"",bb2->getParent() ,bb2);
					bb1->getTerminator()->setSuccessor(j,temp);
					IRBuilder<> IRB(temp); // Will insert the generated instructions BEFORE the first BB instruction	 
					Value *loadAddr = IRB.CreateLoad(bbCounter);
					Value *addAddr = IRB.CreateAdd(loadAddr, ConstantInt::get(Type::getInt32Ty(*Context), edge));
					IRB.CreateStore(addAddr, bbCounter);
					IRB.CreateBr(bb2); // sets new basic block to point to bb2

			    }
			}
		}
	}

	void addBBCounterToTop(std::vector<BasicBlock*> &topo_loop_vector_nested)
	{
		int end = topo_loop_vector_nested.size()-1;
		BasicBlock* firstBB = topo_loop_vector_nested[end];
		IRBuilder<> IRB(firstBB->getFirstInsertionPt());
		Value *loadAddr = IRB.CreateLoad(bbCounter);
		Value *addAddr = IRB.CreateAdd(loadAddr, ConstantInt::get(Type::getInt32Ty(*Context), 0));
		IRB.CreateStore(addAddr, bbCounter);

	}


    bool runOnBasicBlock(BasicBlock &BB) 
    {
 
		IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
		// //this is a place for globalvariable that we definded in the first part of program
		// //previousBlockID, edgeCounter we need two index for two basic block b0->b1
		// //to create edgeCounter we need edge indexes

		Value* zeroIndex = Constant::getNullValue(IntegerType::getInt32Ty(*Context));//everything is in the class fo value

		std::vector<Value*> edgeIndex;
		edgeIndex.push_back(zeroIndex);

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
    
    void addFinalPrintfEdge(BasicBlock& BB)
    {
    	// map<string,GlobalVariable*> edgeCounter;  
    	// edgeCounter is a map from the function name(string) to the address(string)
    	for(auto &function: edgeCounter)
    	{
    		printEdgeCount(BB, function.first, FuncNameToEdges[function.first], function.second);

      	}
    }

    void printEdgeCount(BasicBlock& BB, string funcName, set<pair<string, string>> edges, GlobalVariable* counter) 
    {
      	int i = 0;
      	IRBuilder<> builder(BB.getTerminator());

		for(auto &edge: edges) 
		{

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


    // This function prints path profiling information
     void addFinalPrintfPaths(BasicBlock& BB, LLVMContext *Context, GlobalVariable *pathCounter, Function *printf_func) 
     {
		string output;
		string pathCount;

	    if (totalNumPaths > 1)
	    {
	    	for (int i = 0; i < totalNumPaths; i++)
	    	{
		    	pathCount = to_string(i);
		    	output = "path" + pathCount + ":" + "%d\n";
		    	const char *finalPrintString =  output.c_str();
		    	Constant *pathConst = ConstantDataArray::getString(*Context, finalPrintString);
		    	GlobalVariable *var;
		        var = new GlobalVariable(*(BB.getParent()->getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, pathConst, "PathStr");


			    IRBuilder<> IRB(BB.getTerminator());
				std::vector<Value*> ptr_arrayidx_indices;
			    Value* idxValue = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context),i),ConstantInt::get(Type::getInt32Ty(*Context),0));
			    ConstantInt* const_int64_6 = ConstantInt::get(*Context, APInt(64, StringRef("0"), 10));
				ptr_arrayidx_indices.push_back(const_int64_6);
				ptr_arrayidx_indices.push_back(idxValue);
			    Instruction* ptr_arrayidx = GetElementPtrInst::Create(pathCounter, ptr_arrayidx_indices, "arrayidx", BB.getTerminator());
			    LoadInst* arrayLoadInstruction = new LoadInst(ptr_arrayidx,"loadAddr",false,BB.getTerminator());

			    std::vector<Constant*> indices;
			    Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
			    indices.push_back(zero);
			    indices.push_back(zero);
			    Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
			    
			    CallInst *call = IRB.CreateCall2(printf_func, var_ref, arrayLoadInstruction);
		    	call->setTailCall(false);
	    	}

    	}
    	else
    	{
    		pathCount = to_string(0);
    		output = "path" + pathCount + ":" + "%d\n";
			const char *finalPrintString =  output.c_str();
	    	Constant *pathConst = ConstantDataArray::getString(*Context, finalPrintString);
	    	GlobalVariable *var;
	        var = new GlobalVariable(*(BB.getParent()->getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, pathConst, "PathStr");

			IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
			std::vector<Constant*> indices;
			Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
			indices.push_back(zero);
			indices.push_back(zero);
			Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);

			Value *bbc = builder.CreateLoad(pathCounter);
			CallInst *call = builder.CreateCall2(printf_func, var_ref, bbc);
			call->setTailCall(false);
    	}
    }

 
};
}
    

char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);