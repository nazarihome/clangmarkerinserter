#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/SmallSet.h"
//#include <llvm/ADT/SmallVector.h>
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/CFG.h"
//#include "llvm/Support/InstIterator.h"
//#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>
#include <set>
#include <map>
#include <string.h>
#include <sstream>
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Metadata.h"



#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Metadata.h"

#include <set>
#include <map>
#include <vector>
#include <string.h>
#include <sstream>

using namespace llvm;

namespace {
	
	struct p2 : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		p2() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){
                int changed;			
		int changes = 0;

   		std::vector<Instruction*> instructionList;	//List of instructions
   		std::vector<Instruction*> instructionList2;	//List of instructions
   		std::vector<Instruction*> subList;	//List of instructions

               // do{
                //    changed = 0;	

                    //Put each instruction into list			
                    for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
                            instructionList.insert(instructionList.end(), &*i);
                    }
                
                    
                    
                    //////////////////////////////////////////////////
                    std::map <Instruction*,std::set<Value*>> reachset;
for (Function::iterator BB = F.begin(); BB != F.end(); BB++)  //iterate on BBs
            for (BasicBlock::iterator it = BB->begin(); it != BB->end(); it++) 
                if(StoreInst *inst = dyn_cast<StoreInst>(inst))
                for (Function::iterator BB2 = F.begin(); BB2 != F.end(); BB2++) //iterate on BBs
            for (BasicBlock::iterator it2 = BB->begin(); it2 != BB->end(); it2++){  
                
                for (User::op_iterator op = it2->op_begin(), e = it2->op_end(); op != e; ++op) { 
                    if(((User*)it)->getOperand(0)->getName()==((Value*)&*op)->getName()){
                        
                    reachset[(Instruction*)&*it].insert((Value*)&*op);
                }
            
            }
            }
            
//            if (StoreInst *inst = dyn_cast<StoreInst>(it)) 
//                
//            for (Function::iterator BB2 = F.begin(); BB2 != F.end(); BB2++) //iterate on BBs
//            for (BasicBlock::iterator it2 = BB->begin(); it2 != BB->end(); it2++){  
//             //iterate on instructions
//                  SmallPtrSet<BasicBlock*, 5000> Visited;    
//          //  if(isReachable(it->getParent(),it2->getParent(),Visited))
//             for (User::op_iterator op = it2->op_begin(), e = it2->op_end(); op != e; ++op) { 
//                 if(inst->getPointerOperand()->getName().str()==((Value*)op)->getName().str()){
//                     //reachset[(Instruction*)inst].insert((Instruction*)&*it2);
//                     inst->getPointerOperand()->getName().str();
//                 }
//                   //  
//            }
//            }
//            
//                                      
//            }
                    
                    errs()<<reachset.size()<<"\n";
                    for(std::map <Instruction*,std::set<Value*>>::iterator i =reachset.begin(); i!=reachset.end(); ++i){
                        errs()<<(*i).second.size()<<"\n";
                     for(std::set<Value*>::iterator it=(*i).second.begin();it!=(*i).second.end(),it)   
                        errs()<<(*i).second.getName()<<"\n";
    //                    if(DILocation *Loc = (*i).first->getDebugLoc())
     //                   errs()<<"\n\n"<<"Instruction:"<<Loc->getLine()<<"\n";
                   // for(std::map std::set<Instruction*>::iterator i2 =i.begin(); i2!=i.end(); ++i){
                    //  errs()<<getline(i2)<<"\n";  
                   // }
                    }
                    
                    ///////////////////////////////////////////////////
                    
                    std::set<Instruction*> WorkList;
  for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      WorkList.insert(&*i);
  }
  bool Changed = false;
  const DataLayout &DL = F.getParent()->getDataLayout();
  TargetLibraryInfo *TLI =
      &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();

  while (!WorkList.empty()) {
    Instruction *I = *WorkList.begin();
    WorkList.erase(WorkList.begin());    // Get an element from the worklist...

    if (!I->use_empty())                 // Don't muck with dead instructions...
      if (Constant *C = ConstantFoldInstruction(I, DL, TLI)) {
        // Add all of the users of this instruction to the worklist, they might
        // be constant propagatable now...
//        for (User *U : I->users())
//          WorkList.insert(cast<Instruction>(U));
//////////////
        //   Use &U = *UseList;
           
        // std::set<Instruction*> k=reachset[I];//.begine();
         // for(std::set<Value*>::iterator it=k.begin();it!=k.end();it++)
             //   WorkList.insert(*it);
//////////////
        // Replace all of the uses of a variable with uses of the constant.
     //   I->myreplaceAllUsesWith(C);
       
        // Remove the dead instruction.
        WorkList.erase(I);
        I->eraseFromParent();

        // We made a change to the function...
        Changed = true;
//        ++NumInstKilled;
      }
  }
  return Changed;
                    
                    
                    //////////////////////////////////////////////////
        /*            
                    for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
		       			instructionList2.insert(instructionList2.end(), &*i);
		   		}
                    const DataLayout &TD = F.getParent()->getDataLayout();
                    TargetLibraryInfo *TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();

   			while (!instructionList2.empty()) {
				    	Instruction *I4 = *instructionList2.begin();
				     	instructionList2.erase(instructionList2.begin());    // Get an element from the worklist...
	 
					//Now that made constants, perform constant folding where possible
	     				if (!I4->use_empty()){                 
	       					if (Constant *C = ConstantFoldInstruction(I4, TD, TLI)) {

			 				for (Value::use_iterator UI = I4->use_begin(), UE = I4->use_end(); UI != UE; ++UI){
			   					instructionList2.insert(instructionList2.end(), cast<Instruction>(*UI));
							}
		 
							// Replace all of the uses of a variable with uses of the constant.
							changes+=I4->getNumUses();
							I4->replaceAllUsesWith(C);
		 					changed = 1;
							// Remove the dead instruction.
							instructionList2.erase(std::remove(instructionList2.begin(), instructionList2.end(), I4), instructionList2.end());
							I4->eraseFromParent();
						}
					}
	 
	       			}                    
                            
                            
                            

                                
                }while(changed);                 
                
                
                

			return 1;
         
         */
                }
  
                
		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
			 AU.setPreservesCFG();
      AU.addRequired<TargetLibraryInfoWrapperPass>();
		}
///////////////////////////////////////
   //recursively checking reachable for all successors of src BB               
bool isReachable(BasicBlock *src,BasicBlock *dst,SmallPtrSet<BasicBlock*, 5000> &Visited) {
if(src->getName()==dst->getName())  //same BBs? it's already reached!
		return true;
for (succ_iterator pi = succ_begin(src); pi != succ_end(src); ++pi) {
         
    
  BasicBlock *Succ = *pi;
  if(Visited.count(Succ)) continue;    // Visited makes sure we are not calling reachable twice fore a BB
   Visited.insert(Succ);        
  if(Succ->getName()==dst->getName())
		return true;
   if(isReachable(Succ,dst,Visited)==true)  //reachable from a successor means it's reachable!
		return true;     
    
    
}
              
                
}             
                
 ///////////////////////////////////  




//
                };	
}
char p2::ID = 0;
static RegisterPass<p2> X("p2", "Part 2", true, true);

