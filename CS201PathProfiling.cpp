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
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/PostOrderIterator.h"

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

    GlobalVariable *previousBlockID = NULL;
   
    //FuncNameToBlockNumber is a map from string (function name) to another map which connects to blocknum which is blocks name and their indices :{b0:0,b1:1,..};
    map<string, map<string,int>> FuncNameToBlockNumber;  
    //edgeCounter is a map from the function name(string) to the address(string)
    map<string,GlobalVariable*> edgeCounter;  
    //FuncNameToEdges is a map from function name(string) to a set of pairs
    map<string, set<pair<string,string>>> FuncNameToEdges;  

    CS201Profiling() : FunctionPass(ID) {}


//(*BBI)->printAsOperand(errs(), false);

    bool doInitialization(Module &M) override 
    {
		bool dom;
		std::stack <BasicBlock*> stack;
		std::pair <BasicBlock*, BasicBlock*> backedge_pair;
		std::vector<std::pair<BasicBlock*, BasicBlock*>> backedge_vector; 
		std::vector<std::vector<BasicBlock*>> innerloop_vector;


     	errs() << "Module: " << M.getName() << "\n";

		errs() << "\n---------Starting BasicBlockDemo---------\n";


		//////////// LOOP ALGORITHM START ///////////////////

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
			
			// hacked this from this source because the printf was giving me a segfault
			// https://stackoverflow.com/questions/23929468/identifying-user-define-function-through-llvm-pass
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

			errs() << "BACK EDGES count: " << backedge_count << "\n";

			///////////////// Loop Algorithm from slides ///////////////////////////

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

			// Now check to see if the loop found is the innermost loop
			// if of the loop block items found, if it contains another back edge, toss it because it's not the inner one
			// for each item in loop vector
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
				errs() << "Innermost loop found!" << "\n";
				innerloop_vector.push_back(loop_vector);
				for (unsigned int i = 0; i < innerloop_vector.size(); i++)
				{
					for (unsigned int j = 0; j < innerloop_vector[i].size(); j++)
					{
						BasicBlock* loopitem = innerloop_vector[i][j];
						loopitem->printAsOperand(errs(), false);
						errs() << ",";
					}
				}
			}

			} // end of backedge list
		
	}// end of function loop 
	
	//////////// LOOP END /////////////////////////////

	errs() << "\n";
	errs() << "/////////// EDGE START ///////////////\n\n";

	//////////// EDGE LABEL START /////////////////////////////


	// run algorithm on inner most loop
	// first find reverse topological order
	// go through each vertex in topological order

	//////////// EDGE LABEL END /////////////////////////////

	errs() << "\n";
	errs() << "//////////// EDGE END ///////////////\n\n";

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
     	errs() << "Function: " << F.getName() << '\n';
 	  //	blocks,predecessors,edges,block_ids
 	  	//in each function we need to define the string of blocks that exist in each function
 	  	set<string> blocks;//b0,b1,..

 	  	//for each block we should define predecessors of each block
 	  	map<string,set<string>> predecessors;

 	  	//we should define edges as a pair of two basic blocks(terminator and entry)
 	  	set<pair<string,string>> edges;	

 	  	//we define blocknum as a map from the string name of the block to the block number b0 -> 0
 	  	map<string,int> blocknum;

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


 		for(auto &BB: F) 
 		{
        //  statement BEFORE calling runOnBasicBlock
        	if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator()))
        	{ // major hack?
          		addFinalPrintf(BB);
        	}
        	runOnBasicBlock(BB);
    	}
 
      return true; // since runOnBasicBlock has modified the program
    }
     //-------------------------
//---------
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
    
    void addFinalPrintf(BasicBlock& BB)
    {
    	// map<string,GlobalVariable*> edgeCounter;  
    	// edgeCounter is a map from the function name(string) to the address(string)
    	for(auto &function: edgeCounter)
    	{
    		printEdgeCount(BB, function.first, FuncNameToEdges[function.first], function.second);

      	}
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
 	


      






