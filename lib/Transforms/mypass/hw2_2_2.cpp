

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/ConstantFolding.h"

#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

#include "llvm/IR/User.h""
#include "llvm/IR/Use.h""
#include "llvm/IR/Constants.h"



#include <list>
#include <map>
#include <iostream>
#include <set>
#include <string>

using namespace std;

using namespace llvm;


namespace {

	class My_const_propagation : public FunctionPass {
		public:
		static char ID;
		My_const_propagation(): FunctionPass(ID) {}


		/* all the constants reaching current basic block are recorded in map being passed as argument*/
		void do_const_prop_on_block(map<Value*,Value*> &cvalue_map, BasicBlock &B)
		{

			/* this is INCORRECT implementation of simple constant propagation, with folding */

			for(auto i=B.begin(); i!=B.end();)
			{
				bool ins_deleted=false;

				for(int j=0;j<i->getNumOperands();j++)
				{
					Value * val = i->getOperand(j);
					if(cvalue_map.count(val) >0)
					{
//						if(i->getOpcode()==27) // load -- do not hard code, replace with appropriate call
//						{
                                                   
							//delete the loads, they are not required now
						//////////////////////////////////////
                                                    	//delete the loads, they are not required now
						/////////////////////////////////	
                                                    if (cvalue_map.find(val)!=cvalue_map.end())
                                                    for(auto BB=B.getParent()->begin(); BB!=B.getParent()->end(); BB++){
                                                       SmallPtrSet<BasicBlock*, 5000> Visited; 
                                                       if(isReachable(&B,BB,Visited)){
                                                          errs()<<"eachable to:\n"<<BB->getName()<<"\t";
                                                          for(BasicBlock::iterator it=BB->begin();it!=BB->end();it++){
                                                              Instruction* instr=it;
                                                              if (LoadInst *ldinst = dyn_cast<LoadInst>(instr)){
                                                               for (User::op_iterator op = instr->op_begin(), e = instr->op_end(); op != e; ++op) 
                                                                if((Value*)op==val) (Value*)op=cvalue_map[val];
                                                              //  it->eraseFromParent();
                                                               // ins_deleted = true;
                                                                 errs()<<"Load\n";
                                                               }
                                                              //else
                                                              // for (User::op_iterator op = instr->op_begin(), e = instr->op_end(); op != e; ++op) 
                                                                // if((Value*)op==val) cvalue_map[val]; 
                                                                 
                                                          }
                                                       }
                                                       
                                                   }
                                                    
                                                 ///////////////////////////////////////   
                                                    
                                                    
//                                                    i->replaceAllUsesWith(cvalue_map[val]);
//							i = i->eraseFromParent();							
//							ins_deleted = true;
//							break;
//						}	
//						else
//						{
//                                                    errs()<<"other\n";
//							val->replaceAllUsesWith(cvalue_map[val]);
//						}
					}
				}


				if(!ins_deleted)
				{

					Constant *c = ConstantFoldInstruction(i, i->getModule()->getDataLayout(),NULL);
					if(c)
						errs()<<"Expression evaluates to Const of value : "<<(*c);
					i++;
				}
			}
		}


		map<Value*,Value*>* get_information(BasicBlock &B)
		{
			map<Value*,Value*> *const_map = new map<Value*,Value*>;

			for(auto i=B.begin(); i!= B.end(); i++)
			{
				if(i->getOpcode()!=28) //store
					continue;
				
				for(int j=0;j<i->getNumOperands();j++)
				{
					Value *v = i->getOperand(j);
					
					if(ConstantInt::classof(v))
					{
                                             
						const_map->insert(pair<Value*,Value*> (i->getOperand(j+1), v));
					}
				}
			}

			return const_map;
		}

		bool runOnFunction(Function &F) {

			BasicBlock *bb;
			
			int bb_count=0;
			map<Value*,Value*>* cmap;

			for(auto i=F.begin(); i!=F.end(); i++)
			{
				errs()<<"Original BB ***********************************\n";
				errs()<<(*i)<<"\n";
				errs()<<"Modified BB  ------------------------------------\n";
				if(bb_count>0){ do_const_prop_on_block(*cmap, *i); }
				cmap = get_information(*i);
				bb_count++;
				errs()<< (*i)<< "\n";
				errs()<<"BB over ------------------------------------\n";
			}

			return true;

		}

		void getAnalysisUsage(AnalysisUsage &AU) const override {
			AU.setPreservesAll();
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
	};

}



char My_const_propagation::ID = 0;
static RegisterPass<My_const_propagation> Z("My_const_propagation", "My analysis pass");

