//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//



#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/ilist.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/Trace.h"
#include "llvm/ADT/StringExtras.h"

#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/IR/Dominators.h>
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include <llvm/ADT/SmallVector.h>
#include "llvm/Analysis/PostDominators.h"

#include "llvm/IR/Metadata.h"
#include "llvm/IR/DebugInfo.h"

#include <PathCache.cpp>
#include <list>
#include <vector>
#include <map>
#include <string>
#include <algorithm>

#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */

using namespace std;
using namespace llvm;



namespace {
  // Hello - The first implementation, without getAnalysisUsage.
  struct path_finder : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    path_finder() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
    set<Loop*> LoopsList,OuterLoopList;
    map<Loop*,int> loopMap;
    LoopInfo &LI=getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    errs()<<F;
    for(LoopInfo::iterator i=LI.begin(), e=LI.end();i!=e;++i){
        Loop* L=*i;
        OuterLoopList.insert(L);
        LoopsList.insert(L);
        errs()<<*(L->getHeader())<<"\n";

      }
    int change=0;
    do{
        set<Loop*>::iterator it=LoopsList.begin();
        change =0;
        while (it!=LoopsList.end()){
            Loop* L=*it;
            for(Loop::iterator lIt=L->begin();lIt!=L->end();lIt++){
                int numbefore=0;
                int numafter=0;
                numbefore=LoopsList.size();
                
                LoopsList.insert(*lIt);
                numafter=LoopsList.size();
                if(numbefore!=numafter)
                change=1;
                
            }
            it++;
        }
    }while(change==1);
    int count=0;
    for(set<Loop*>::iterator it=LoopsList.begin();it!=LoopsList.end();it++){
        errs()<<*(*it)<<"\n";
        loopMap[*it]=count;
        count++;
    }
    BasicBlock* entrance=&(F.getEntryBlock());
    set<BasicBlock*> exitBBSet;
    for(Function::iterator BB=F.begin();BB!=F.end();BB++){
        if(succ_begin(BB)==succ_end(BB)){
            exitBBSet.insert(BB);
        }
    }
    set<PathList> allpaths;
    PathCache pc_;
    for(set<BasicBlock*>::iterator it=exitBBSet.begin();it!=exitBBSet.end();it++){
        PathList paths;
        paths=pc_.findAllSimplePaths(entrance, (*it),false,false);
        pc_.dumpPaths(paths);
        allpaths.insert(paths);
    }
    int pathcount=0;
    set<vector<Loop*>> briefLoopPathSet;
    for(set<PathList>::iterator it=allpaths.begin();it!=allpaths.end();it++){
        PathList paths=*it;
        
        for (auto & pathid : paths) {
            vector<Loop*> briefLoopPath;
            pathcount++;
            errs()<<"**********************************************\n";
            errs()<<"Path "<<pathcount<<"\n";
            errs()<<"**********************************************\n";
            Path path = pc_.extractPath(pathid);
            vector<BasicBlock*> tempPath;
            for (auto block : path) {
                Loop* loop=LI.getLoopFor(block);
                
                BasicBlock* bb=block;
                //errs()<< bb->getName().str()<<"\n";
                tempPath.insert(tempPath.end(),bb);
            }
            vector<BasicBlock*> tempCompletePath;
            completePath(tempPath,tempCompletePath);
            
            for(int j=0;j<tempCompletePath.size();j++){
                errs()<<tempCompletePath[j]->getName().str()<<"->";
            }
            errs()<<"\n";
            list<Loop*> pathLoops;
            int bbcounter=0;
            for(int j=0;j<tempCompletePath.size();j++){
                BasicBlock* block=tempCompletePath[j];
                Loop* loop=LI.getLoopFor(block);
                bbcounter++;
                Loop* front=pathLoops.front();
                BasicBlock* bb=block;
                errs()<<bb->getName().str()<<"\n";
                if(front!=loop){
                    
                    pathLoops.push_front(loop);

                    if(loop!=NULL){
                        Loop* ploop=loop->getParentLoop();
                        if(ploop==NULL)
                            ploop=loop;
                        errs()<<"After "<<bbcounter<<"\n";
                        errs()<<"\n\n"<<"In "<<loop->getLoopDepth ()<<" "<<*ploop<<"\n";
                        errs() << "In loop in line: " << getLine(loop->getHeader()->begin())<<" outermost loop in "<<
                        getLine(ploop->getHeader()->begin())<<"\n";
                        briefLoopPath.insert(briefLoopPath.end(),loop);
                        
//                        for(Loop::iterator lIt=loop->begin();lIt!=loop->end();lIt++){
//                            Loop* subloop=*lIt;
//                            errs()<<*subloop<<"\tin depth of:\t";//<<subloop->getLoopDepth ()<<"\n" ;
//                        }
                    }else {
                        briefLoopPath.insert(briefLoopPath.end(),loop);
                        errs()<<"After "<<bbcounter<<"\n\n"<<"sequential"<<"\n";
                    }
                    bbcounter=0;
                }
               
            }
            
            briefLoopPathSet.insert(briefLoopPath);
        }
    }
    errs()<<"**********************************************\n";
    errs()<<"**********************************************\n";
    errs()<<"Loop based Paths\n";
    errs()<<"**********************************************\n";
    errs()<<"**********************************************\n";
    pathcount=0;
    for(set<vector<Loop*>>::iterator sit=briefLoopPathSet.begin();sit!=briefLoopPathSet.end();sit++){
        vector<Loop*> pvec=*sit;
        pathcount++;
        errs()<<"**********************************************\n";
        errs()<<"Path "<<pathcount<<"\n";
        errs()<<"**********************************************\n";
        for(int i=0;i<pvec.size();i++){
            Loop* loop=pvec[i];
            if(loop==NULL)
                errs()<<"sequential\n";
            else{
                Loop* ploop=loop->getParentLoop();
                if(ploop==NULL)
                    ploop=loop;
                
                errs()<<"\n\n"<<"In "<<loop->getLoopDepth ()<<" "<<*ploop<<"\n";
                errs() << "In loop in line: " << getLine(loop->getHeader()->begin())<<" outermost loop in "<<
                getLine(ploop->getHeader()->begin())<<"\n";
                
                
            }
                
            
            
        }
        
    }
    
      return false;
    }
    
    
    unsigned getLine(Instruction* iInst) {
            if (DILocation * Loc = iInst->getDebugLoc())
                return Loc->getLine();
            else
                return 0;
    }
    
    
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.setPreservesAll();
        AU.addRequired<PostDominatorTree>();
        AU.addRequired<LoopInfoWrapperPass>();
        AU.addRequired<DominatorTreeWrapperPass>();
    }

    void completePath(vector<BasicBlock*>& path_init,vector<BasicBlock*>& path_out){
        for(int i=0;i<path_init.size()-1;i++){
            BasicBlock* bb=path_init[i];
            path_out.insert(path_out.end(),bb);
            vector<BasicBlock*> tempPath;
            SmallPtrSet<const BasicBlock*, 5000> Visited;
            //errs()<<"call comp for:\t"<<(path_init[i])->getName().str()<<"and "<<(path_init[i+1])->getName().str()<<"\n";
            singlePath(path_init[i],path_init[i+1],Visited,&tempPath);
//            for(int j=0;j<tempPath.size();j++){
//                errs()<<tempPath[j]->getName().str()<<"->";
//            }
            //errs()<<"\n";
            for(int j=tempPath.size()-1;j>0;j--){
               path_out.insert(path_out.end(),tempPath[j]);

            }
            
           
        }
        path_out.insert(path_out.end(),path_init[path_init.size()-1]);

    }
    bool singlePath(BasicBlock *src,BasicBlock *dst,SmallPtrSet<const BasicBlock*, 5000> &Visited,vector<BasicBlock*>* path) {
        if(src->getName()==dst->getName()){  //same BBs? it's already reached!
            return true;
        }
        for (succ_iterator pi = succ_begin(src); pi != succ_end(src); ++pi) {


            BasicBlock *Succ = *pi;
            if(Visited.count(Succ)) continue;    // Visited makes sure we are not calling reachable twice fore a BB
            Visited.insert(Succ);        
            if(Succ->getName()==dst->getName())
                return true;
            if(singlePath(Succ,dst,Visited,path)==true){  //reachable from a successor means it's reachable!
                path->insert(path->end(),Succ);
                return true;     
            }
    
    
        }

    return false;
    }

//    
    
    
    
    
    
  };
}

char path_finder::ID = 0;
static RegisterPass<path_finder> X("path_finder", "path_finder");


