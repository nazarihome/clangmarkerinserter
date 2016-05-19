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
#include <string.h>
#include <sstream>


using namespace llvm;
using namespace std;



namespace {

  struct Assignment_4: public FunctionPass {
    static char ID;
    int change;
    Assignment_4() : FunctionPass(ID) {change=0;}
   
    bool runOnFunction(Function &F) override {
     //data structure to keep BBdata for every block
      map<BasicBlock*, set<Value*>>   killset;  //kill set 
      map<BasicBlock*, set<Value*>>   genset;   //gen set
      map<BasicBlock*, set<Value*>>   BBInSet;  //input set
     
     //now we need to iterate over all BBs and create all the 
     //sets needed for analysis.
        for (Function::iterator BB = F.begin(); BB != F.end(); BB++) { //iterate on BBs
            for (BasicBlock::iterator it = BB->begin(); it != BB->end(); it++) { //iterate on instructions
                if (StoreInst *inst = dyn_cast<StoreInst>(it)) {//check if it's a store
                   
                  
                    Value* tmp=inst->getPointerOperand();
                 //   errs()<<tmp->getName().str()<<"\n";
                   killset[BB].insert((inst->getPointerOperand()));
                  }
                if (LoadInst *inst = dyn_cast<LoadInst>(it)) {//check if it's a load
                    Value* tmp=inst->getPointerOperand();
                    genset[BB].insert((inst->getPointerOperand()));
                   // errs()<<tmp->getName().str()<<"\n";
                    

                }
            }
        }



       
       
 
             
       
     int count=1;  
      int FoundAssignment = 0;
     set<Value*> tmpglobal;//to prevent deadlock by due to having two phases
     set<Value*> uninit; //
      do {
        FoundAssignment = false;


        do {
          change = 0;
           for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
             set<Value*> tmp;
             tmp=BBInSet[BB];  //temprary to check for change after one iteration
          for (succ_iterator it = succ_begin(BB); it != succ_end(BB); it++) {
             for (set<Value*>::iterator v=BBInSet[*it].begin(); v!=BBInSet[*it].end(); ++v) 
 
                myunion(&BBInSet[BB],&BBInSet[*it]);
            }
                
                 mysubtract(&BBInSet[BB],&killset[BB]);
                myunion(&BBInSet[BB],&genset[BB]); 
               
                
                ///Chaeck for change
              for (set<Value*>::iterator it=tmp.begin(); it!=tmp.end(); ++it) {
                 if (BBInSet[BB].find(*it)==BBInSet[BB].end()) {
                     change=1;
                 //errs()<<BB->getName()<<"here1\n";
                 }
                
              }
                 for (set<Value*>::iterator it=BBInSet[BB].begin(); it!=BBInSet[BB].end(); ++it) {
                     if (tmp.find(*it)==tmp.end()) {
                         change=1;
                         //errs()<<BB->getName()<<"here1\n";
                     }
                 }
            
////////////////////////////////////////  errs() << "here\n" ;

 ///////////////////////////////////
          }
        
        } while(change!=0);
 
 //////////////////////////////////////////////////////////////       
// for (set<Value*>::iterator it=tmpglobal.begin(); it!=tmpglobal.end(); ++it) 
//    if (BBInSet[&(F.getEntryBlock())].find(*it)==BBInSet[&(F.getEntryBlock())].end()) {FoundAssignment=1;errs()<<F.getEntryBlock().getName()<<"here1\n";}
//                
// for (set<Value*>::iterator it=BBInSet[&(F.getEntryBlock())].begin(); it!=BBInSet[&(F.getEntryBlock())].end(); ++it) 
//    if (tmpglobal.find(*it)==tmpglobal.end()) {FoundAssignment=1;errs()<<F.getEntryBlock().getName()<<"here1\n";}
//            
//      errs()<<"last: ";        
//     for (set<Value*>::iterator ii=BBInSet[&(F.getEntryBlock())].begin(); ii!=BBInSet[&(F.getEntryBlock())].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }    
//      errs()<<"\nnow:";
//   for (set<Value*>::iterator ii=tmpglobal.begin(); ii!=tmpglobal.end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//            errs()<<"\n";
         tmpglobal=BBInSet[&(F.getEntryBlock())];     
         if (count==1)uninit=BBInSet[&(F.getEntryBlock())];
         errs()<<"In function "<< F.getName() << ":\n"<<  "Variables which are not initialized:\t";
      for (set<Value*>::iterator it=BBInSet[&(F.getEntryBlock())].begin(); it!=BBInSet[&(F.getEntryBlock())].end(); ++it) {
        errs() <<(*it)->getName() <<"\t";
          
      }
          errs()<<"\n";
///////////////////////////////////////////////////////////////        
//        
//        for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
//                errs()<<BB->getName()<<"\n";
//       errs()<<"killset: "; 
//      for (set<Value*>::iterator ii=killset[BB].begin(); ii!=killset[BB].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//       errs()<<"genset: "; 
//      for (set<Value*>::iterator ii=genset[BB].begin(); ii!=genset[BB].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//       errs()<<"inset: "; 
//      for (set<Value*>::iterator ii=BBInSet[BB].begin(); ii!=BBInSet[BB].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//       errs()<<"\n\n\n";
//       }

//now finding assignment by uninitialized variable
        change = 0;
        do {
          change = 0;
          set<Value*> &entryBlockDataInValue =BBInSet[&(F.getEntryBlock())];
          for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
          for (BasicBlock::iterator ldins = BB->begin(); ldins != BB->end(); ldins++){  // go through all instructions in BB
              if (LoadInst *inst = dyn_cast<LoadInst>(ldins)) //find if it's a load
                if (entryBlockDataInValue.find(inst->getPointerOperand()) != entryBlockDataInValue.end())  // look if it's operand is unsound
                  for (Value::user_iterator users = inst->user_begin(); users != inst->user_end(); users++) //through all values that used it 
                    if (StoreInst *instStore = dyn_cast<StoreInst>(*users))                    //if any of them is stor means it's assignment
                      if (entryBlockDataInValue.find(instStore->getPointerOperand()) == entryBlockDataInValue.end()) {
                        entryBlockDataInValue.insert(instStore->getPointerOperand());                         //we should add that into BBInset as uninitialized
                        change = 1;
                      }
           }
         }
        } while(change!=0);
   count++;
//         for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
//                errs()<<BB->getName()<<"\n";
//       errs()<<"killset: "; 
//      for (set<Value*>::iterator ii=killset[BB].begin(); ii!=killset[BB].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//       errs()<<"genset: "; 
//      for (set<Value*>::iterator ii=genset[BB].begin(); ii!=genset[BB].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//       errs()<<"inset: "; 
//      for (set<Value*>::iterator ii=BBInSet[BB].begin(); ii!=BBInSet[BB].end(); ++ii) {
//          errs()<< (*ii)->getName()<<" ";
//      }
//       errs()<<"\n";
//       }
  // if(count==1)return 1;
      }while(FoundAssignment!=0);

      
      
 
//////////////////////////////////////////////////////////////////////////////////
      //errs()<<"In function "<< F.getName() << ":\n";
      errs() <<  "Unsound variables:\t";
      for (set<Value*>::iterator it=BBInSet[&(F.getEntryBlock())].begin(); it!=BBInSet[&(F.getEntryBlock())].end(); ++it) {
        if(uninit.find(*it)==uninit.end())errs()<<(*it)->getName() <<"\t";
          
      }

      errs()<<"\n";
      return false;
    
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

char Assignment_4::ID = 0;
static RegisterPass<Assignment_4> X("Assignment_4", "Unsoundness Check");