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
      map<Value*,set<BasicBlock*>> BBSet;       //map of value and BB which it's generated in
      map<BasicBlock*, set<Value*>>   BBuninit; 
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
                    BBSet[(inst->getPointerOperand())].insert(BB);
                   // errs()<<tmp->getName().str()<<"\n";
                    

                }
            }
        }



       
       
 
             
       
     int count=1;  
      int FoundAssignment = 0;
     set<Value*> tmpglobal;//to prevent deadlock by due to having two phases
     set<Value*> uninit; //

        do {
          change = 0;
           for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
             set<Value*> tmp;
             tmp=BBInSet[BB];  //temprary to check for change after one iteration
          for (succ_iterator it = succ_begin(BB); it != succ_end(BB); it++) {
             for (set<Value*>::iterator v=BBInSet[*it].begin(); v!=BBInSet[*it].end(); ++v) 
 
                myunion(&BBInSet[BB],&BBInSet[*it]);
            }
                
              
                myunion(&BBInSet[BB],&genset[BB]); 
                  mysubtract(&BBInSet[BB],&killset[BB]);
                
                ///Check for change
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
 
 
         tmpglobal=BBInSet[&(F.getEntryBlock())];     
         if (count==1)uninit=BBInSet[&(F.getEntryBlock())];
       //  errs()<<"In function "<< F.getName() << ":\n"<<  "***Variables which are not initialized:\n";
      for (set<Value*>::iterator it=BBInSet[&(F.getEntryBlock())].begin(); it!=BBInSet[&(F.getEntryBlock())].end(); ++it) {
       // errs() <<(*it)->getName() <<" used in ";
       for (set<BasicBlock*>::iterator it2=BBSet[*it].begin(); it2!=BBSet[*it].end(); ++it2)  
       {
     //      errs()<<(*it2)->getName()<<" ";
        BBuninit[*it2].insert(*it);
      //  errs() <<(*it)->getName()<<"\n";
       }
             errs()<<"\n";
          
      }
         
        //  errs()<<"\n";
///////////////////////////////////////////////////////////////        


//now finding assignment by uninitialized variable
  

         
    ////////////////////////////////////////////////     
       map<BasicBlock*, set<Value*>>   ukillSet;  //kill set 
      map<BasicBlock*, set<Value*>>   ugenSet;   //gen set
      map<BasicBlock*, set<Value*>>   uBBInSet;  //input set
      map<Value*,set<BasicBlock*>> uBBSet;       //map of value and BB which it's generated in

            do { //iterate if a new unsound has found
          change = 0;
          
 //making the new kill and gen sets
 for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
  for (BasicBlock::iterator it = BB->begin(); it != BB->end(); it++) {
     if (LoadInst *inst = dyn_cast<LoadInst>(it)) //it's load so we can check for gen set
      // If loading from uninit value
      if ((BBuninit[BB].find(inst->getPointerOperand()) != BBuninit[BB].end()) || \
           (uBBInSet[BB].find(inst->getPointerOperand()) != uBBInSet[BB].end() ) )
        for (Value::user_iterator ui = inst->user_begin(); ui != inst->user_end(); ui++) {
          //assgnment an uninitialized to a variable, makes itunsound
          if (StoreInst *stinst = dyn_cast<StoreInst>(*ui))
            if ((stinst->getParent()) == (BB))
              if (ugenSet[BB].find(stinst->getPointerOperand()) == ugenSet[BB].end()) {
                ugenSet[BB].insert(stinst->getPointerOperand());
              }
          //assignment to anuninitialized to itself makes it unsound
          if (Instruction *instChain = dyn_cast<Instruction>(*ui))
            for (Value::user_iterator ui = instChain->user_begin(); ui != instChain->user_end(); ui++)
              if (StoreInst *stinst = dyn_cast<StoreInst>(*ui))
                if ((stinst->getParent()) == (&*BB))
                  if (ugenSet[BB].find(stinst->getPointerOperand()) == ugenSet[BB].end()) {
                    ugenSet[BB].insert(stinst->getPointerOperand());
                  }    
        }                      
    //Now check stores for other
        if (StoreInst *inst = dyn_cast<StoreInst>(it))//it's store so add it to kill set
            
        if (ugenSet[BB].find(inst->getPointerOperand()) == ugenSet[BB].end())
        if (ukillSet[BB].find(inst->getPointerOperand()) == ukillSet[BB].end())
        ukillSet[BB].insert(inst->getPointerOperand());
  }
}
          //same as finding uninitialized but forward

           for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
             set<Value*> tmp;
             tmp=uBBInSet[BB];  //temprary to check for change after one iteration
          for (pred_iterator it = pred_begin(BB); it != pred_end(BB); it++) {
             for (set<Value*>::iterator v=uBBInSet[*it].begin(); v!=uBBInSet[*it].end(); ++v) 
 
                myunion(&uBBInSet[BB],&uBBInSet[*it]);
            }
                
                 mysubtract(&uBBInSet[BB],&ukillSet[BB]);
                myunion(&uBBInSet[BB],&ugenSet[BB]); 
               
                
                ///Check for change
              for (set<Value*>::iterator it=tmp.begin(); it!=tmp.end(); ++it) {
                 if (uBBInSet[BB].find(*it)==uBBInSet[BB].end()) {
                     change=1;
                 //errs()<<BB->getName()<<"here1\n";
                 }
                
              }
                 for (set<Value*>::iterator it=uBBInSet[BB].begin(); it!=uBBInSet[BB].end(); ++it) {
                     if (tmp.find(*it)==tmp.end()) {
                         change=1;
                         //errs()<<BB->getName()<<"here1\n";
                     }
                 }

                
////////////////////////////////////////  errs() << "here\n" ;

 ///////////////////////////////////
          }
       
        } while(change!=0);
 
        
        ////print out results
        errs()<<"In function "<< F.getName() << ":\n";
     for (Function::iterator BB = F.begin(); BB != F.end(); BB++) {
          errs() <<BB->getName()<<":\n\n";
            errs() << "Uninitialized Values :\t";

      for (set<Value*>::iterator it=BBuninit[BB].begin(); it!=BBuninit[BB].end(); ++it)
        errs() << (*it)->getName()<< "\t";
      errs() << "\n"; 
         
         errs() << "Unsound Values :\t";

      for (set<Value*>::iterator it=uBBInSet[BB].begin(); it!=uBBInSet[BB].end(); ++it)
        errs() << ((*it)->getName()).str() << "\t";
      errs() << "\n\n";   
      
         
     }          
        
        
        
//      ////////////////////////////////////////
//   
//   
//////////////////////////////////////////
      
               
                       

      
 
//////////////////////////////////////////////////////////////////////////////////
     
          
          //errs()<<"In function "<< F.getName() << ":\n";
//      errs() <<  "Unsound variables:\t";
//      for (set<Value*>::iterator it=BBInSet[&(F.getEntryBlock())].begin(); it!=BBInSet[&(F.getEntryBlock())].end(); ++it) {
//        if(uninit.find(*it)==uninit.end())errs()<<(*it)->getName() <<"\t";
//          
//      }
//
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