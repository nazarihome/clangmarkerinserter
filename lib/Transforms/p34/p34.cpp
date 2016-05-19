

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

///////////////////////////////////////////////////
namespace {

  struct my_stats {
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
}

///////////////////////////////////////////////////////
namespace {
	
	struct p34 : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		p34() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){
const Function::BasicBlockListType &BBs = F.getBasicBlockList();
BasicBlock* src;
BasicBlock* dst;
int nBB=0;
Function::iterator bi=F.begin();
int randn;
srand (time(NULL));
Function::iterator be;

for (Function::iterator bi=F.begin(), be = F.end(); bi != be; bi++) {
nBB++;
}
randn = rand() % nBB + 1;
src=(bi);
src+=randn;
randn = rand() % nBB + 1;
dst=(bi);
dst+=+randn;
isReachable(src,dst);
		}
bool isReachable(BasicBlock *src,BasicBlock *dst) {
succ_iterator e= succ_end(src);
for (succ_iterator pi = succ_begin(src); pi != e; ++pi) {
         if(*pi==dst)
		return true;
        }
for (succ_iterator pi = succ_begin(src); pi != e; ++pi) {
         if(isReachable(src,dst)==true)
		return true;
        }
return false;
}




		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      			
		}

	};
}

char p34::ID = 0;
static RegisterPass<p33> R("p34", "Part 3.4", true, true);

