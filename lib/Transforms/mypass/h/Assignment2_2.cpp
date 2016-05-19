///this program prints out reaching definitions for constant folding
///this means that it only prints out values with only one constant reaching 
///definition which can be substituted by constant
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Metadata.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Constants.h"
#include <limits>
#include <map>
#include <set>
#include <string.h>
#include <sstream>
#include "llvm/Analysis/ConstantFolding.h"

using namespace llvm;
using namespace std;


namespace {
 
  struct Assignment_2_2: public FunctionPass {
    static char ID;
    Assignment_2_2() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
int change=0;       
 int count=0;     
do{
    ///iteratively finding reaching definitions, constant propagate, constant fold until there is no change 
 count++;   
change=0;
map<BasicBlock*, map<Value*, set<Value*> >> ValueSet ;    //keeping reaching values(includes constants and none constants))
map<BasicBlock*, map<Value*, set<uint64_t> >> constSet; //keeping reaching values which are constant
    
RD(F ,ValueSet,constSet);   // finding reaching definitions   
     

  errs() << "********************\t iteration:"<<count<<"\t***************\n"; 
for (Function::iterator BB = F.begin(); BB != F.end(); BB++){
/////////////////////////////////////
////////////     Printing reaching definitions in each iteration
    errs()<< "In BB "<<(*BB).getName()<< ":\n\n";
//   errs() << "ConstantMap Values in iteration "<<count<<" are:\n"; 
for (map<Value*, set<Value*> >::iterator it=ValueSet[BB].begin(); it!=ValueSet[BB].end(); ++it){
        if(it->second.size()==1) {
            
            errs()<<(it->first)->getName().str()<<":\t";
        for (set<Value*>::iterator itSet=(it->second).begin(); itSet!=(it->second).end(); ++itSet)
           if (ConstantInt* CI = dyn_cast<ConstantInt>(*itSet))errs() << " " <<*CI;
        errs() << "\n"; 
        }
        
}     
   errs() << "\n"; 
 /////////////////////////////////////////       
        
        for (BasicBlock::iterator iInst = BB->begin(); iInst != BB->end(); iInst++) {
         
            
          for(unsigned int oprandNum=0; oprandNum<(iInst->getNumOperands()); oprandNum++) {
         
              
             
            Value* operandValue = iInst->getOperand(oprandNum);
            map<Value*, set<Value*> >::iterator tmp = ValueSet[BB].find(operandValue);
            map<Value*, set<uint64_t> >::iterator tmp2 = constSet[BB].find(operandValue);
            if (ValueSet[BB].find(operandValue) !=  ValueSet[BB].end()){
                
              if (((ValueSet[BB].find(operandValue)->second).size() == 1 )) {     ///// checkin for each operand 
                                                                                  ////if there is only one constant value reaching
                  //do replacement as suggested in example
                  
                Value *v = *((ValueSet[BB].find(operandValue)->second).begin());
                bool instDelete = false;
               // errs()<< "size: " << (tmp->second).size()<<"\n";
                if (ConstantInt* CI = dyn_cast<ConstantInt>(v)) {
                 //   errs()<< operandValue->getName()<<" subs with "<< dyn_cast<ConstantInt>(v)->getLimitedValue()<<"\n";
                  //Now mapped value has 1 reaching definition, it is constant, and we are not in generating 
                  if(LoadInst *inst = dyn_cast<LoadInst>(iInst)) { //load

                    errs() << "!!Replacement Happened: '" <<*inst << "' replaced with '"  << *v << "' and got deleted\n";
                    iInst->replaceAllUsesWith(v);
                    iInst = iInst->eraseFromParent();
                    instDelete = true;   
                    change=1;                           //sth has changed
                    break;
                  }
                  else {
                    if (AllocaInst *inst = dyn_cast<AllocaInst>(operandValue)) //we don't want to touch allocations
                      break;
                    if (AllocaInst *inst = dyn_cast<AllocaInst>(iInst))      
                      break;
                    
                                        errs() << "!!Replacement Happened: '" <<*inst << "' replaced with '"  << *v << "'\n";
                    operandValue->replaceAllUsesWith(v);
                    change=1;                               //sth has changed
                  }
                }

                if (!instDelete) {
                  Constant *c = ConstantFoldInstruction(iInst, iInst->getModule()->getDataLayout(),NULL);
                  if(c)
                    errs()<<"Expression evaluates to Const of value : "<<(*c);
                }
                
              
              }
          }
          }



        }
    // printbeforeafter(BB);

}
////////////////////////////////////////
//    for (Function::iterator BB = F.begin(); BB != F.end(); BB++){
//        errs()<< (*BB)<< "\n";
//        errs() << "\n\tConstantMap Values in iteration "<<count<<":\n";
//        for (map<Value*, set<Value*> >::iterator it=ValueSet[BB].begin(); it!=ValueSet[BB].end(); ++it){
//            
//        for (set<Value*>::iterator itSet=(it->second).begin(); itSet!=(it->second).end(); ++itSet)
//          if (ConstantInt* CI = dyn_cast<ConstantInt>(*itSet))errs() << "\n" <<*CI;
//        errs() << "\n"; 
//        }
//            
//    }
//    
     //////////////////////////////////
  

      
    }while(change!=0) ;   
    
//    for (Function::iterator BB = F.begin(); BB != F.end(); BB++){
//     errs()<<"Modified BB  ------------------------------------\n";
//				
//				errs()<< (*BB)<< "\n";
//				errs()<<"BB over ------------------------------------\n";
//    }
     //////////////////////////////////

      return true;
    }
    void printbeforeafter(BasicBlock *b){
     
			
        
    }
    void RD(Function &F, 
    map<BasicBlock*, map<Value*, set<Value*> >> &ValueSet ,
    map<BasicBlock*, map<Value*, set<uint64_t> >> &constSet) {
      for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
          //there is no kill set so just iterate and keep any value which is stored
        for (BasicBlock::iterator it = BB->begin(); it != BB->end(); it++) 
            
          if (StoreInst *inst = dyn_cast<StoreInst>(it)) {
            string operandName =  ((inst->getPointerOperand())->getName()).str();
            
          
            Value *v = inst->getOperand(0);
            //errs()<<v->getName()<<"\n";
            //map<Value*, set<uint64_t> > tmp=ValueSet[BB];
            ValueSet[BB][inst->getPointerOperand()].insert(v);
            if (ConstantInt* ConstInt = dyn_cast<ConstantInt>(v)) {     //if it is constant also keep it in constant
              map<Value*, set<uint64_t> > tmp2=constSet[BB];  
              tmp2[inst->getPointerOperand()].insert(ConstInt->getLimitedValue());
              

            }
          }

      }

///to handle back edges we have to do this iteratively but still not killing any value, just keep them
      int change = 0;
      do {
        change = 0;
        for (Function::iterator BB = F.begin(); BB != F.end(); BB++) 
          for (pred_iterator predIt = pred_begin(BB); predIt != pred_end(BB); predIt++) {
 
            for (map<Value*, set<uint64_t> >::iterator it=constSet[*predIt].begin(); it!=constSet[*predIt].end(); ++it)
              for (set<uint64_t>::iterator itSet=(it->second).begin(); itSet!=it->second.end(); ++itSet)
                if (constSet[BB][it->first].find(*itSet) == constSet[BB][it->first].end()) {
                  constSet[BB][it->first].insert(*itSet);
                  change = 1;
                }
            for (map<Value*, set<Value*> >::iterator it=ValueSet[*predIt].begin(); it!=ValueSet[*predIt].end(); ++it)
              for (set<Value*>::iterator itSet=(it->second).begin(); itSet!=(it->second).end(); ++itSet)
                if (ValueSet[BB][it->first].find(*itSet) == ValueSet[BB][it->first].end()) {
                  ValueSet[BB][it->first].insert(*itSet);
                  change = 1;
                }
          }
      } while(change!=1);

    }
///my set operations
   void myunion(set<Value*>* out,set<Value*>* in){
          
        for (set<Value*>::iterator it=in->begin(); it!=in->end(); ++it) {
           
            if(out->find(*it)==out->end()){
                out->insert(*it);
                 
            }
                
        }  
      }
     
       void mysubtract(set<Value*>* out,set<Value*>* in){
          
        for (set<Value*>::iterator it=in->begin(); it!=in->end(); ++it) {
            if(out->find(*it)!=out->end() ){
                //errs()<< "\n"<<(*it)->getName()<<" ";
                out->erase(*it);
                
                
            }
                
        }  
      }
 


  };
}

char Assignment_2_2::ID = 0;
static RegisterPass<Assignment_2_2> X("Assignment_2_2", "Assignment_2_2");
