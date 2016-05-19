



#define DEBUG_TYPE "mytests"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/User.h"

#include "llvm/IR/Dominators.h"    


#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DataLayout.h"

#include "llvm/IR/DebugInfo.h"
#include "llvm/Pass.h"

#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/MemoryBuiltins.h"


#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"

#include "llvm/Analysis/TargetLibraryInfo.h"

#include <stack>
#include <deque>
#include <map>

using namespace llvm;

namespace {




    struct ArrayInfo {
        long top_limit;
        long bottom_limit;
        Value* dynSize;
        unsigned typeSize;        
    };

    void dumpArrayInfoMap(std::map<Value*, ArrayInfo*>* map) {
        for(std::map<Value*, ArrayInfo*>::iterator it=map->begin(); it!=map->end();it++) {
            errs() << "\n====== ";
            it->first->dump();
            errs() << "\ttop_limit: " << it->second->top_limit 
                   << "\n\tbottom_limit: " << it->second->bottom_limit;
            if(it->second->dynSize!=NULL) {
                errs() << "\n\tdynSize: "; 
                it->second->dynSize->dump();
            }
            else
                errs() <<"\n\tdynSize: NULL\n"; 

            errs() << "\ttypeSize: " << it->second->typeSize << "\n";
        }
    }

    // Calculate now many * are there for the pointer
    // Eq. int** x; will return 2  
    int calPointerDepth(Type* type) {
        int depth = 1;
        
        if(!type->isPointerTy())
            return 0;
        SequentialType* seqType = static_cast<SequentialType*>( type );
        while(seqType->getElementType()->isPointerTy()) {
            depth++;
            seqType =  static_cast<SequentialType*>( seqType->getElementType() ); 
        }
        return depth;
    }

    // Assume the input type is ArrayType which is a static multidimension array
    // Eq. int x[10][20] will return 200 in size
    long calArraySize(Type* type) {
        if(type->getTypeID()==Type::ArrayTyID) {
            ArrayType *a = static_cast<ArrayType*>( type );
            long size = a->getNumElements();

            while(a->getElementType()->isArrayTy()) {
                a = static_cast<ArrayType*>( a->getElementType() );
                size *= a->getNumElements();
            }

            return size;
        }
        else if(type->getTypeID()==Type::IntegerTyID) {
#ifdef DEBUG
            errs() << "[calArraySize] What to do with integer type? "; type->dump(); errs() << "\n";
#endif
            return 0;    
        }
        else {
#ifdef DEBUG
            errs()<< "[calArraySize] Can not handle this case!\n";
#endif
            return 0;
        }
    }
struct Project : public FunctionPass {
static char ID;
//////////////////////////

std::map<Value*,  ArrayInfo*> arrayMap;

//////////////////////////
Project() : FunctionPass(ID) {}

/////////////////////////////////
/////////////////////////////////

        
        /*******************************************************************/
        /* Functions for basic array bound check with constant upper bound */
        /*******************************************************************/
        void insertBoundCheck(Instruction* inst,  GetElementPtrInst *GEP, unsigned num_array_elems){
#ifdef PRINT_REMOVE_INFO
            errs() << "[insertBoundCheck-static] limit: " << num_array_elems <<", GEP: "; GEP->dump();
#endif

            // Create bounds-checking function call's prototype
            Type* ArgTypes_i64_u64[3];
            Type* ArgTypes_i32_u64[3];
            Type* ArgTypes_i64_u32[3];
            Type* ArgTypes_i32_u32[3];

            Type *VoidTy = Type::getVoidTy(inst -> getContext());
            IntegerType *Int64Ty = Type::getInt64Ty(inst -> getContext());
            IntegerType *Int32Ty = Type::getInt32Ty(inst -> getContext());

            ArgTypes_i64_u64[0] = ArgTypes_i64_u32[0] = Int64Ty;
            ArgTypes_i32_u64[0] = ArgTypes_i32_u32[0] = Int32Ty;

            ArgTypes_i64_u64[1] = ArgTypes_i64_u32[1] = Int64Ty;
            ArgTypes_i32_u64[1] = ArgTypes_i32_u32[1] = Int64Ty;

            ArgTypes_i64_u64[2] = ArgTypes_i32_u64[2] = Int64Ty;
            ArgTypes_i64_u32[2] = ArgTypes_i32_u32[2] = Int32Ty;

            ArrayRef<Type*> arg_types_i32_u64(ArgTypes_i32_u64, 3);
            ArrayRef<Type*> arg_types_i32_u32(ArgTypes_i32_u32, 3);
            ArrayRef<Type*> arg_types_i64_u64(ArgTypes_i64_u64, 3);
            ArrayRef<Type*> arg_types_i64_u32(ArgTypes_i64_u32, 3);

            FunctionType *ChkType_i64_u64 = FunctionType::get(VoidTy, arg_types_i64_u64, false);
            //FunctionType *ChkType_i64_u32 = FunctionType::get(VoidTy, arg_types_i64_u32, false);
            FunctionType *ChkType_i32_u64 = FunctionType::get(VoidTy, arg_types_i32_u64, false);
            //FunctionType *ChkType_i32_u32 = FunctionType::get(VoidTy, arg_types_i32_u32, false);

            // Insert or retrieve the checking function into the program Module
            Module *M = inst->getParent()->getParent()->getParent();
            Constant *Chk_i64_u64 = M->getOrInsertFunction("__checkArrayBounds_i64_u64", ChkType_i64_u64);
            //Constant *Chk_i64_u32 = M->getOrInsertFunction("__checkArrayBounds_i64_u32", ChkType_i64_u32);
            Constant *Chk_i32_u64 = M->getOrInsertFunction("__checkArrayBounds_i32_u64", ChkType_i32_u64);
            // Constant *Chk_i32_u32 = M->getOrInsertFunction("__checkArrayBounds_i32_u32", ChkType_i32_u32);


            unsigned num_gep_operands = GEP->getNumOperands();
            // Create the arguments list 
            Value* args[3];
            //Index
            if(num_gep_operands==3)
                args[0] = GEP -> getOperand (2);
            else if(num_gep_operands==2)
                args[0] = GEP -> getOperand (1);
            else {
#ifdef DEBUG                
                errs() << "[insertBoundCheck] Warning! wrong num of arguments!\n";
#endif
            }

            //Min
            args[1] = ConstantInt::get(Int64Ty, 0);
            //Max
            args[2] = ConstantInt::get(Int64Ty, num_array_elems);

            CallInst *hook;
            // Create Array Reference to the function arguments
            ArrayRef<Value*> func_args(args, 3);

            if(args[0]->getType()->getIntegerBitWidth() == 64){

                // Create the function call
                hook = CallInst::Create(Chk_i64_u64, func_args, "");
                // Insert the function call
                hook->insertAfter(inst);

            }else if (args[0]->getType()->getIntegerBitWidth() == 32){

                // Create the function call
                hook = CallInst::Create(Chk_i32_u64, func_args, "");
                // Insert the function call
                hook->insertAfter(inst);

            } else{
#ifdef DEBUG
                errs() << "Shouldn't come here\n";
#endif
            }
        }

        /******************************************************************/
        /* Functions for basic array bound check  with dynamic upper bound*/
        /******************************************************************/

        void insertBoundCheck(Instruction* inst,  GetElementPtrInst *GEP, Value* num_array_elems){
#ifdef PRINT_REMOVE_INFO
            errs() << "[insertBoundCheck-dynamic] \n\tlimit: "; num_array_elems->dump(); errs() <<"\tGEP: "; GEP->dump();
#endif
            // Create bounds-checking function call's prototype
            Type* ArgTypes_i64_u64[3];
            Type* ArgTypes_i32_u64[3];
            Type* ArgTypes_i64_u32[3];
            Type* ArgTypes_i32_u32[3];

            Type *VoidTy = Type::getVoidTy(inst -> getContext());
            IntegerType *Int64Ty = Type::getInt64Ty(inst -> getContext());
            IntegerType *Int32Ty = Type::getInt32Ty(inst -> getContext());

            ArgTypes_i64_u64[0] = ArgTypes_i64_u32[0] = Int64Ty;
            ArgTypes_i32_u64[0] = ArgTypes_i32_u32[0] = Int32Ty;

            ArgTypes_i64_u64[1] = ArgTypes_i64_u32[1] = Int64Ty;
            ArgTypes_i32_u64[1] = ArgTypes_i32_u32[1] = Int64Ty;

            ArgTypes_i64_u64[2] = ArgTypes_i32_u64[2] = Int64Ty;
            ArgTypes_i64_u32[2] = ArgTypes_i32_u32[2] = Int32Ty;

            ArrayRef<Type*> arg_types_i32_u64(ArgTypes_i32_u64, 3);
            ArrayRef<Type*> arg_types_i32_u32(ArgTypes_i32_u32, 3);
            ArrayRef<Type*> arg_types_i64_u64(ArgTypes_i64_u64, 3);
            ArrayRef<Type*> arg_types_i64_u32(ArgTypes_i64_u32, 3);

            FunctionType *ChkType_i64_u64 = FunctionType::get(VoidTy, arg_types_i64_u64, false);
            FunctionType *ChkType_i64_u32 = FunctionType::get(VoidTy, arg_types_i64_u32, false);
            FunctionType *ChkType_i32_u64 = FunctionType::get(VoidTy, arg_types_i32_u64, false);
            FunctionType *ChkType_i32_u32 = FunctionType::get(VoidTy, arg_types_i32_u32, false);

            // Insert or retrieve the checking function into the program Module
            Module *M = inst->getParent()->getParent()->getParent();
            Constant *Chk_i64_u64 = M->getOrInsertFunction("__checkArrayBounds_i64_u64", ChkType_i64_u64);
            Constant *Chk_i64_u32 = M->getOrInsertFunction("__checkArrayBounds_i64_u32", ChkType_i64_u32);
            Constant *Chk_i32_u64 = M->getOrInsertFunction("__checkArrayBounds_i32_u64", ChkType_i32_u64);
            Constant *Chk_i32_u32 = M->getOrInsertFunction("__checkArrayBounds_i32_u32", ChkType_i32_u32);


            unsigned num_gep_operands = GEP->getNumOperands();
            // Create the arguments list 
            Value* args[3];
            //Index
            if(num_gep_operands==3)
                args[0] = GEP -> getOperand (2);
            else if(num_gep_operands==2)
                args[0] = GEP -> getOperand (1);
            else {
#ifdef DEBUG
                errs() << "[insertBoundCheck] Warning! wrong num of arguments!\n";
#endif
            }
            //Min
            args[1] = ConstantInt::get(Int64Ty, 0);
            //Max
            args[2] = num_array_elems;

            CallInst *hook;
            // Create Array Reference to the function arguments
            ArrayRef<Value*> func_args(args, 3);

            if(args[0]->getType()->getIntegerBitWidth() == 64 && args[2]->getType()->getIntegerBitWidth() == 64){

                // Create the function call
                hook = CallInst::Create(Chk_i64_u64, func_args, "");
                // Insert the function call
                hook->insertAfter(inst);

            }else if (args[0]->getType()->getIntegerBitWidth() == 32 && args[2]->getType()->getIntegerBitWidth() == 64 ){

                // Create the function call
                hook = CallInst::Create(Chk_i32_u64, func_args, "");
                // Insert the function call
                hook->insertAfter(inst);

            }else if (args[0]->getType()->getIntegerBitWidth() == 64 && args[2]->getType()->getIntegerBitWidth() == 32 ){

                // Create the function call
                hook = CallInst::Create(Chk_i64_u32, func_args, "");
                // Insert the function call
                hook->insertAfter(inst);

            }else if (args[0]->getType()->getIntegerBitWidth() == 32 && args[2]->getType()->getIntegerBitWidth() == 32 ){

                // Create the function call
                hook = CallInst::Create(Chk_i32_u32, func_args, "");
                // Insert the function call
                hook->insertAfter(inst);

            } else{
#ifdef DEBUG
                errs() << "Shouldn't come here\n";
#endif
            }
        }

        void processAllocateInst(Instruction* inst, DataLayout &dLayout) {
            AllocaInst* alloca = static_cast<AllocaInst*>( (Instruction*)inst );

            // This is static array declaration, int x[10]
            if( alloca->getType()->getElementType()->isArrayTy() ) {
                ArrayType *a = static_cast<ArrayType*>( alloca->getType()->getElementType() );
                ArrayInfo* info = new struct ArrayInfo;
                info->top_limit = calArraySize(a);
                info->bottom_limit = 0;
                info->dynSize = NULL;
                info->typeSize =  dLayout.getTypeAllocSize(inst->getOperand(0)->getType());
                arrayMap.insert( std::pair<Value*, ArrayInfo*>(inst, info) );
            }
            // This is just a pointer declaration, need to capture malloc to get the size
            else if( alloca->getType()->getElementType()->isPointerTy() ) {
                ArrayInfo* info = new struct ArrayInfo;
                info->top_limit = -1;
                info->bottom_limit = -1;
                 info->dynSize = NULL;
                info->typeSize =  dLayout.getTypeAllocSize(inst->getOperand(0)->getType());
                arrayMap.insert( std::pair<Value*, ArrayInfo*>(inst, info) );
            }
        }

        void processCallInst(Instruction* inst, DataLayout &dLayout, TargetLibraryInfo &tlInfo) {
            CallInst* call = static_cast<CallInst*>( (Instruction*)inst );

            // Check for dynamic array declaration
            if( isAllocationFn(call, &tlInfo) ) {   // Assume it is dynamic array declaration with constant size
                Value* arraySize = getMallocArraySize(call, dLayout, &tlInfo);
    
                ConstantInt* size = NULL;
                if( arraySize->getValueID()==Value::ConstantIntVal )
                    size = static_cast<ConstantInt*>( getMallocArraySize(call, dLayout, &tlInfo) );
                else {
                    Instruction* ttInst = static_cast<Instruction*>(arraySize);
                    arraySize = getInstLoad(ttInst);
                }

                std::stack<Value*> stack;
                stack.push(inst);
                while(stack.size()!=0) {
                    Value* tempValue = stack.top();
                    stack.pop();

                    for(Value::use_iterator use = tempValue->use_begin(); use != tempValue->use_end(); ++use) {
                        Instruction* tempInst =(Instruction*) (Value*)( *use );  
                            //Instruction* tempInst = dyn_cast<Instruction*>( use);
                        if( tempInst->getOpcode()==Instruction::Store) {
                            std::map<Value*, ArrayInfo*>::iterator it = arrayMap.find( tempInst->getOperand(1) );
                            if(it!=arrayMap.end()) {
                                if(size!=NULL)
                                    it->second->top_limit = size->getSExtValue();
                                else
                                    it->second->dynSize = arraySize;
                                it->second->bottom_limit = 0;
                            }
                            else {
#ifdef DEBUG
                                errs() << "Cannot find store target!\n";
#endif
                            }
                        }
                        else
                            stack.push(*use);
                    }
                }
            }
        }

        void processGEP(Instruction* inst, Function &F) {
            unsigned num_array_elems;

            GetElementPtrInst *GEP = static_cast<GetElementPtrInst*>( (Instruction*)inst);
            std::map<Value*, ArrayInfo*>::iterator it = arrayMap.find(GEP->getPointerOperand());

            if(it!=arrayMap.end()) {
                Type * ptr_type =   GEP->getPointerOperandType()->getPointerElementType() ;
                num_array_elems = cast<ArrayType>(ptr_type) -> getNumElements() ;
                insertBoundCheck(inst, GEP, num_array_elems);
            }
            else {
                Instruction* tempInst = static_cast<Instruction*>( GEP->getPointerOperand() );

                if( tempInst->getOpcode()==Instruction::Load ) {
                     std::map<Value*, ArrayInfo*>::iterator it2 = arrayMap.find( tempInst->getOperand(0) );
                    if( it2!=arrayMap.end() ) {
                        if(it2->second->top_limit!=-1)
                            insertBoundCheck(inst, GEP, it2->second->top_limit);
                        else if(it2->second->dynSize!=NULL)
                            insertBoundCheck(inst, GEP, it2->second->dynSize);
                        else {
#ifdef DEBUG
                            errs() << "\tWARNING! Can not find the size of the array. Skip insert boundary check. " << GEP->getParent()->getName() << ", "; GEP->dump();
#endif
                        }    
                    }
                    else {
#ifdef DEBUG
                        errs() << "\tWARNING 1! Haven't considered this case!\n";
#endif
                    }
                }
                else if( tempInst->getOpcode()==Instruction::GetElementPtr) {
                    GetElementPtrInst* GEP2 = static_cast<GetElementPtrInst*>( tempInst );
                    Instruction* tempInst2 = static_cast<Instruction*>( GEP2->getPointerOperand() );

                    std::map<Value*, ArrayInfo*>::iterator it3 = arrayMap.find(tempInst2);
                    if(it3!=arrayMap.end()) {
                        Type * ptr_type =   GEP2->getPointerOperandType()->getPointerElementType() ;
                        num_array_elems = cast<ArrayType>(ptr_type) -> getNumElements() ;
                        insertBoundCheck(inst, GEP, num_array_elems);
                    }
                    else {
                        GetElementPtrInst* GEP3 = static_cast<GetElementPtrInst*>( tempInst2 );
                        Instruction* tempInst3 = static_cast<Instruction*>( GEP3->getPointerOperand() );

                        std::map<Value*, ArrayInfo*>::iterator  it4 = arrayMap.find( tempInst3 );
                        if( it4!=arrayMap.end() ) {
                            if(it4->second->top_limit!=-1)
                                insertBoundCheck(inst, GEP, it4->second->top_limit);
                            else if(it4->second->dynSize!=NULL)
                                insertBoundCheck(inst, GEP, it4->second->dynSize);
                            else {
#ifdef DEBUG
                                errs() << "\tWARNING 2! Can not find the size of the array! "; GEP->dump();
#endif
                            }
                        }
                        else {
#ifdef DEBUG
                            errs() << "\tWARNING 3! Haven't considered this case!\n";
#endif
                        }
                    }
                }
            }
        }

        Value* getInstLoad(Value* value) {
            std::stack<Value*> stack;

            stack.push(value);
            while( !stack.empty() ) {
                Value* tempValue = stack.top();
                stack.pop();

                if(LoadInst::classof(tempValue))
                    return tempValue;

                if(Instruction::classof(tempValue)) {
                    Instruction* tempInst = static_cast<Instruction*>(tempValue);
                    for(unsigned i=0;i<tempInst->getNumOperands();i++) {
                        stack.push(tempInst->getOperand(i));
                    }
                }
            }

            return NULL;
        }
        
       virtual void getAnalysisUsage(AnalysisUsage &AU) const {
            AU.setPreservesAll();
      AU.addRequired<TargetLibraryInfoWrapperPass>();
            //AU.addRequired<DataLayout>();
            //AU.addRequired<LoopInfo>();

            AU.addRequired<DominatorTreeWrapperPass>();

            AU.addRequired<DominanceFrontier>();
            AU.addRequired<PostDominatorTree>();
        }


        virtual bool runOnFunction(Function &F) {
            errs() << "\n=============================================\n";
            errs() << "[ runOnFunction - " << F.getName() << " ]\n";
            errs() << "=============================================\n";


            Module* M=F.getParent();
            // Create meta data for instructions
            TargetLibraryInfo tlInfo = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
            
            DataLayout dLayout =M->getDataLayout();
            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    if( inst->getOpcode()==Instruction::Alloca ) {  // Check for static array or pointer declaration
                        processAllocateInst(inst, dLayout);
                    }
                    else if( inst->getOpcode()==Instruction::Call ) { 
                        processCallInst(inst, dLayout, tlInfo);
                    }
                }
            }



           

            // Insert bound checks
            errs() << "\n*** Start inserting bound checks ***\n";
            long insertedChecks = 0;
            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    if( inst->getOpcode()==Instruction::GetElementPtr ) { // Check for pointer element access

                        Instruction * inst_copy = inst;



                        if(inst_copy){
                            processGEP(inst, F);
                            insertedChecks++;
                        }
#ifdef DEBUG
                        else{
                            errs() << "Do NOT insert checks for ";
                            inst->dump();
                        }
#endif
                    }
                }
            }

            errs() << "[End runOnFunction] - inserted " << insertedChecks << " checks\n";

            return false;
        }



//////////////////////////////
///////////////////////////////











}; 

}
//std::map<Value*,  ArrayInfo*> Project::arrayMap;

// Static variables for Part2 - Global eliminate



char Project::ID = 0;
// Register Project pass command
static RegisterPass<Project> X("project", "project tests");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     