

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/ilist.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/Trace.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/IR/Dominators.h>
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include <llvm/ADT/SmallVector.h>
#include "llvm/Analysis/PostDominators.h"

#include <list>
#include <vector>
#include <map>
#include <string>
#include <algorithm>

#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */

using namespace std;
using namespace llvm;
#define DEBUG_TYPE "hello"


STATISTIC(HelloCounter, "Counts number of functions greeted");

////////////////////////////////////////////////////////////////////
/// Data structure required for stats  /////////////////////////////
////////////////////////////////////////////////////////////////////
namespace {

  struct my_stats {     //integer stats
    int min, max, total;
     my_stats() {
      max = total = 0;
	min=1000;
    }
    void add(int a) {
      if (a < min) min = a;
      if (a > max) max = a;
      total += a;
    }
    
  };
   struct my_dstats {   //Double stats
    double min, max, total;
     my_dstats() {
      max = total = 0;
	min=1000;
    }
    void add(double a) {
      if (a < min) min = a;
      if (a > max) max = a;
      total += a;
    }
    
  };
}


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
////////////////  PART 2 ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

namespace {

  struct p2 : public FunctionPass  {
    
      //stat variables
	int funccounter;        
	my_stats* dominatorstats =new my_stats;
	my_stats* loopstats =new my_stats;
	my_stats* outerloopstats =new my_stats;
	my_stats* BBinloopstats =new my_stats;
	my_stats* loopoutCFGstats=new my_stats;
	my_stats* BBstats=new my_stats;
        my_stats* edgebackcounter=new my_stats;
        my_stats* edgestats=new my_stats;
    static char ID; 
		p2() : FunctionPass(ID) {funccounter=0;}
	virtual ~p2(){
            //printing out stats
                errs() << "\nTotal Function Count:                    " << funccounter;
                errs() << "\n";
                errs() << "\nMax BBs in a Function:                   " << BBstats->max;
                errs() << "\nMin BBs in a Function:                   " << BBstats->min;
                errs() << "\nAverage BBs in a Function:               " << BBstats->total/funccounter;
                errs() << "\n";
                errs() << "\nMax edges in a Function CFG:             " << edgestats->max;
                errs() << "\nMin edges in a Function CFG:             " << edgestats->min;
                errs() << "\nAverage edges in a Function:             " << edgestats->total/funccounter;
                errs() << "\n";
                errs() << "\nMax backedge Per Function:           " << edgebackcounter->max;
                errs() << "\nMin backedge Per Function:           " << edgebackcounter->min;
                errs() << "\nAverage backedge Per Function:       " << edgebackcounter->total/funccounter;
                errs() << "\n";
                errs() << "\nMax number of BB in loops:           " << BBinloopstats->max;
                errs() << "\nMin number of BB in loops:           " << BBinloopstats->min;
                errs() << "\nAverage number of BB in loops:       " << BBinloopstats->total/funccounter;
		//errs() << "\n total	"<< BBinloopstats->total;
                errs() << "\n";
		errs() << "\nMax Dominators Per BasicBlock:           " << dominatorstats->max;
                errs() << "\nMin Dominators Per BasicBlock:           " << dominatorstats->min;
                errs() << "\nAverage Dominators Per BasicBlock:       " << dominatorstats->total/BBstats->total;
		//() << "\n total	"<< dominatorstats->total;
		//errs() <<"\n func  numbet	"<<funccounter;
                errs() << "\n";
		
                
}

    virtual bool runOnFunction(Function &F) {
      
      funccounter++;
      edgestats->add(edgeCount(&F));// Counting edges count
      //functionName(&F);
      getInfo(F);                   //  Rest of stats
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfoWrapperPass>();

AU.addRequired<DominatorTreeWrapperPass>();
    }

    void getInfo(Function& F)  {
//******
LoopInfo &LI=getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
//**********************
int edgebacklocal=0;            //Counting Back edges using LoopInfo
for(LoopInfo::iterator i=LI.begin(), e=LI.end();i!=e;++i){

Loop* L=*i;
edgebacklocal+=L->getNumBackEdges();    //
}
edgebackcounter->add(edgebacklocal);
//*****************
int outerloopcounter=0;
int loopcounter=0;
for(LoopInfo::iterator i=LI.begin(), e=LI.end();i!=e;++i){

Loop* L=*i;

for(Loop::block_iterator bb=L->block_begin();bb!=L->block_end();++bb){
 SmallVector<std::pair< const BasicBlock*, const BasicBlock*>,50> Edges;
L->getExitEdges(Edges);
int size=0;
while(!Edges.empty()){
Edges.pop_back ();

size++;
}
loopoutCFGstats->add(size);
}
//*****************

int BBcounter=0;
outerloopcounter++;
loopcounter += countSubLoops(L);
for(Loop::block_iterator bb=L->block_begin();bb!=L->block_end();++bb){
BBcounter+=1;

}
BBinloopstats->add(BBcounter);
}

loopstats->add(loopcounter);
outerloopstats->add(outerloopcounter);

//*******
int numBB=0;
for (Function::iterator BBs = F.begin(); BBs != F.end(); BBs++) numBB++;
BBstats->add(F.size());
for (Function::iterator BBs = F.begin(); BBs != F.end(); BBs++) {
 DominatorTreeBase<BasicBlock> *dominatorTree;
 dominatorTree = new DominatorTreeBase<BasicBlock>(false);
 dominatorTree->recalculate(F);
   int dominateCount = 0;

for (Function::iterator it = F.begin(); it != F.end(); it++) {
					if((dominatorTree->dominates(it,BBs))==true){
						dominateCount++;
					}
	}
dominatorstats->add(dominateCount);
}

    };

    bool functionName(Function *F) {
      errs().write_escaped(F->getName()) << '\n';
      return false;
    }
/////////////////////////////////////
int countSubLoops(Loop *L)
		{
			int loopCount = 1;
			if(!L->empty())
			{
				for(LoopInfoBase<BasicBlock, Loop>::iterator LI = L->begin(), LI_end = L->end(); LI != LI_end; ++LI)
				{
					Loop* L_in = *LI;
					loopCount += countSubLoops(L_in);
				}
			}			
			return loopCount;
		}
///////////////////////////////////////
int edgeCount (const Function* F) {
      int edgeCount = 0;
      for (Function::const_iterator bi=F->begin(), be = F->end(); bi != be; bi++) {
        const BasicBlock *BB = bi.getNodePtrUnchecked ();
	//This allows me to see all paths from BB to other Basic Blocks.
        for (succ_const_iterator pi = succ_begin(BB), e = succ_end(BB); pi != e; ++pi) {
          edgeCount++;
        }
      }
      return edgeCount;
    }
  };
}

char p2::ID = 1;
static RegisterPass<p2> A("Assignment_2", "Part 2", false, false);


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
////////////////  PART 3.1 ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
// it's redundant with part 2 to seperate passes from each other



namespace {

  struct p31 : public FunctionPass  {
    
	int funccounter;
	my_stats* dominatorstats =new my_stats;
	my_stats* loopstats =new my_stats;
	my_stats* outerloopstats =new my_stats;
	my_stats* BBinloopstats =new my_stats;
	my_stats* loopoutCFGstats=new my_stats;
	my_stats* BBstats=new my_stats;
        my_stats* edgebackcounter=new my_stats;
        my_stats* edgestats=new my_stats;
    static char ID; 
		p31() : FunctionPass(ID) {funccounter=0;}
	virtual ~p31(){
                errs() << "\nTotal Function Count:                    " << funccounter;
                errs() << "\n";
                errs() << "\nMax BBs in a Function:                   " << BBstats->max;
                errs() << "\nMin BBs in a Function:                   " << BBstats->min;
                errs() << "\nAverage BBs in a Function:               " << BBstats->total/funccounter;
                errs() << "\n";
                errs() << "\nMax number of loops:           " << loopstats->max;
                errs() << "\nMin number of loops:           " << loopstats->min;
                errs() << "\nAverage number of loops:       " << loopstats->total/funccounter;
		//errs() << "\n total	"<< loopstats->total;
		
                errs() << "\n";
		errs() << "\nMax number of outer loops:           " << outerloopstats->max;
                errs() << "\nMin number of outer loops:           " << outerloopstats->min;
                errs() << "\nAverage number of outer loops:       " << outerloopstats->total/funccounter;
		//errs() << "\n total	"<< outerloopstats->total;
		
                errs() << "\n";
		errs() << "\nMax number of edges exit the loop:           " << loopoutCFGstats->max;
                errs() << "\nMin number of  edges exit the loop:           " << loopoutCFGstats->min;
                errs() << "\nTotal number of  edges exit the loop:       " << loopoutCFGstats->total;
		//errs() << "\n total	"<< BBinloopstats->total;
                errs() << "\n";
                
}

    virtual bool runOnFunction(Function &F) {
        
	funccounter++;
         edgestats->add(edgeCount(&F));
  
      getInfo(F);
      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      AU.addRequired<PostDominatorTree>();
	AU.addRequired<LoopInfoWrapperPass>();

AU.addRequired<DominatorTreeWrapperPass>();
    }

    void getInfo(Function& F)  {
//******
LoopInfo &LI=getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
//**********************
int edgebacklocal=0;
for(LoopInfo::iterator i=LI.begin(), e=LI.end();i!=e;++i){

Loop* L=*i;
edgebacklocal+=L->getNumBackEdges();
}
edgebackcounter->add(edgebacklocal);
//*****************
//iteration through loops and get how many exit edges they have
int outerloopcounter=0;
int loopcounter=0;
for(LoopInfo::iterator i=LI.begin(), e=LI.end();i!=e;++i){

Loop* L=*i;


 SmallVector<std::pair< const BasicBlock*, const BasicBlock*>,50> Edges;
L->getExitEdges(Edges);
int size=0;

while(!Edges.empty()){
Edges.pop_back ();

size++;
}
loopoutCFGstats->add(size);
}
//*****************
//itteration through outer loops
for(LoopInfo::iterator i=LI.begin(), e=LI.end();i!=e;++i){
    Loop* L=*i;
int BBcounter=0;
outerloopcounter++;
//counting all the loops
loopcounter += countSubLoops(L);
for(Loop::block_iterator bb=L->block_begin();bb!=L->block_end();++bb){
BBcounter+=1;   //itteration through BB in outer loops

}
BBinloopstats->add(BBcounter);
}

loopstats->add(loopcounter);
outerloopstats->add(outerloopcounter);

//*******
//counting number of dominators in functions
int numBB=0;
for (Function::iterator BBs = F.begin(); BBs != F.end(); BBs++) numBB++;
BBstats->add(numBB);
//nested iteration to see any domination possibility
for (Function::iterator BBs = F.begin(); BBs != F.end(); BBs++) {
 DominatorTreeBase<BasicBlock> *dominatorTree;
 dominatorTree = new DominatorTreeBase<BasicBlock>(false);
 dominatorTree->recalculate(F);
   int dominateCount = 0;

for (Function::iterator it = F.begin(); it != F.end(); it++) {
					if((dominatorTree->dominates(it,BBs))==true){
						dominateCount++;
					}
	}
dominatorstats->add(dominateCount);
}

    };


/////////////////////////////////////
    //counting all the loops recursively
int countSubLoops(Loop *L)
		{
			int loopCount = 1;
			if(!L->empty())
			{
				for(LoopInfoBase<BasicBlock, Loop>::iterator LI = L->begin(), LI_end = L->end(); LI != LI_end; ++LI)
				{
					Loop* L_in = *LI;
					loopCount += countSubLoops(L_in);
				}
			}			
			return loopCount;
		}
///////////////////////////////////////
int edgeCount (const Function* F) {
      int edgeCount = 0;
      for (Function::const_iterator bi=F->begin(), be = F->end(); bi != be; bi++) {
        const BasicBlock *BB = bi.getNodePtrUnchecked ();
	//This allows me to see all paths from BB to other Basic Blocks.
        for (succ_const_iterator pi = succ_begin(BB), e = succ_end(BB); pi != e; ++pi) {
          edgeCount++;
        }
      }
      return edgeCount;
    }
  };
}

char p31::ID = 1;
static RegisterPass<p31> B("Assignment_3_1", "Part 3.1", false, false);


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
////////////////  PART 3.2 ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

namespace {
  struct p32: public FunctionPass {
    static char ID;
    my_stats* warshalcycles =new my_stats;
    int funccounter;
    p32() : FunctionPass(ID) {funccounter=0;}
~p32(){
    errs() << "\nMax Warshal cycles per function::                   " << warshalcycles->max;
                errs() << "\nMin Warshal cycles per function::                   " << warshalcycles->min;
                errs() << "\nAverage Warshal cycles per function::               " << warshalcycles->total/funccounter;
                errs() << "\n";
    
}
       
    virtual bool runOnFunction(Function &F)  {
        funccounter++;
        int maxid=0; 
      //We need a hash table to assign ID to BBs  
      map<BasicBlock*, int> hash;
      set <pair<int, int>> cycles; // The cycle set
       int Bid= 0;
      for (Function::iterator pi = F.begin(); pi != F.end(); pi++) {
        hash.insert( pair<BasicBlock*, int>(pi, Bid) );
        Bid++;
        maxid++;
      }
      
      
      bool **table = new bool*[maxid];
      //    Creating the transient cycle matrix
      for ( int row=0; row<maxid; row++) {
        table[row] = new bool[maxid];
        for ( int col=0; col<maxid; col++)
          table[row][col] = 0;
      }
     for (Function::iterator bBlock = F.begin(); bBlock != F.end(); bBlock++) {
        int row_index = hash[bBlock];
        for (succ_iterator succIt = succ_begin(bBlock); succIt != succ_end(bBlock); succIt++) {
          int col_index = hash[*succIt];
          table[row_index][col_index] = 1; //   if there is a path, update with 1
        }
      }

     // now we go through the matrix and update it if there is a a path 
     // between i and j through k
      for (int row=0; row<maxid; row++)
        for (int k1=0; k1<maxid; k1++)
          if (table[row][k1])
            for (int k2=0; k2<maxid; k2++)
              if (table[k2][row])
                table[k2][k1] = 1;
        
      for ( int Bid=0; Bid<maxid; Bid++)
        for ( int k=0; k<maxid; k++)
        if (table[Bid][k] && table[k][Bid])   // path from i to j and j to i?
          if (Bid != k) {
            cycles.insert(pair<int,int>(Bid, k));
            cycles.insert(pair<int,int>(k, Bid));
           
          }

     // errs() << "Number of Warshal cycles: " << cycles.size() / 2 << "\n";
      warshalcycles->add(cycles.size()/2);


    return false;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const {
    }

  };
}
char p32::ID = 0;
static RegisterPass<p32> E("Assignment_3_2", "Part 3.2", true, true);


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
////////////////  PART 3.3 ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

namespace {
	
	struct p33 : public FunctionPass {
		
		static char ID; 
		p33() : FunctionPass(ID) {}

		
		virtual bool runOnFunction(Function &F){
			
                    errs()<<F.getName()<<"\n";
      		PostDominatorTree& PDT = getAnalysis<PostDominatorTree>();

			// iteration through all BB vs all BB
                for (Function::iterator it1=F.begin() ; it1 != F.end(); it1++) {
                    for (Function::iterator it2=F.begin() ; it2 != F.end(); it2++) {

                        
                        if(PDT.dominates(it2,it1)==false){  //  It doesn't postdominate the otherBB
                                                       
                      
                            for (succ_iterator pi = succ_begin(it2); pi != succ_end(it2); ++pi) {   // it does post dominate at least one of its successors (difinitly not all)
                                if(PDT.dominates(it1,*pi))
                                    errs()<<it1->getName()<<"\tis control dependent on\t"<<it2->getName()<<"\n";
                            }
                        }
                    }
                    
                    
}        
                        
return false;					
			

			
		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      			AU.addRequired<PostDominatorTree>();	//init request
		}

	};
}

char p33::ID = 0;
static RegisterPass<p33> C("Assignment_3_3", "Part 3.3", true, true);


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
////////////////  PART 3.4 ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

namespace {
	
	struct p34 : public FunctionPass {
		
		static char ID;
                int funcnum;
                my_dstats* timestats =new my_dstats;
		p34() : FunctionPass(ID) {srand (time(NULL));
                funcnum=0;
                }

	virtual ~p34(){
            if (funcnum!=0){
		errs() << "\nMax time to test 1e6 reachability accross functions:           " << timestats->max<<" Second";
                errs() << "\nMin time to test 1e6 reachability accross functions:           " << timestats->min<<" Second";
                errs() << "\nAverage time to test 1e6 reachability accross functions:       " << timestats->total/funcnum<<" Second";
		
		
                errs() << "\n";
            }
            else{
                errs()<<"no function to test reachability!\n";
            }
            }
		
		virtual bool runOnFunction(Function &F){
                    funcnum++;
const Function::BasicBlockListType &BBs = F.getBasicBlockList();
Function::iterator src;
Function::iterator dst;
int nBB=0;
Function::iterator bi=F.begin();
int randn;
srand (time(NULL));
Function::iterator be;

for (Function::iterator bi=F.begin(), be = F.end(); bi != be; bi++) {
nBB++;
}

    clock_t start;
    double duration;
start = clock();
for(int i=0;i<1000000;i++){
 src=F.begin();
 dst=F.begin();
 
 randn = rand() % nBB ;

 for(int j=0;j<randn;j++)src++;

 randn = rand() % nBB ;
 for(int j=0;j<randn;j++)dst++;

 
SmallPtrSet<const BasicBlock*, 5000> Visited;
//if (isReachable(src,dst,Visited))
   // errs()<<src->getName()<<"\treached\t"<<dst->getName()<<"    \n";
//else 
   // errs()<<src->getName()<<"\tdidn't reach\t"<<dst->getName()<<"    \n";
}
duration = ( clock() - start ) / (double) CLOCKS_PER_SEC;
timestats->add(duration);
		}
                
  //recursively checking reachable for all successors of src BB               
bool isReachable(BasicBlock *src,BasicBlock *dst,SmallPtrSet<const BasicBlock*, 5000> &Visited) {
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

         
return false;
}




		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      			
		}

	};
}

char p34::ID = 0;
static RegisterPass<p34> D("Assignment_3_4", "Part 3.4", true, true);
/////////////////////////////////////////////////////////////////////


























