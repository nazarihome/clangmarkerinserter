
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

/////////////////////////////////////
// Define this when using llvm 3.4 //
/////////////////////////////////////
#define PART2_LOCAL_ELIMINATION


#define DEBUG_TYPE "mytests"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/User.h"

#ifdef  LLVM_3_4
#include "llvm/Analysis/Dominators.h"
#else
#include "llvm/IR/Dominators.h"    
#endif

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DataLayout.h"

#include "llvm/DebugInfo.h"
#include "llvm/Pass.h"

#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/MemoryBuiltins.h"


#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"

#include "llvm/Target/TargetLibraryInfo.h"

#include <deque>
#include <map>

using namespace llvm;

namespace {


// NOTE: Only one of these defines can be set!


//#define DEBUG
//#define PRINT_REMOVE_INFO

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
        static char ID; // Pass identification, replacement for typeid
        static std::map<Value*, ArrayInfo*> arrayMap;

        
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
                Value* arraySize = getMallocArraySize(call, &dLayout, &tlInfo);
    
                ConstantInt* size = NULL;
                if( arraySize->getValueID()==Value::ConstantIntVal )
                    size = static_cast<ConstantInt*>( getMallocArraySize(call, &dLayout, &tlInfo) );
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
                        Instruction* tempInst = static_cast<Instruction*>( *use );  

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
        

        /************************************/
        /* Functions for global elimination */
        /************************************/
        struct enhancedCFG {
            std::deque<Instruction*> checkBounds;
            std::deque<Instruction*> usedIndex;
            std::deque<Instruction*> storeList;

            // Standard data flow 
            std::deque<Instruction*> IN;
            std::deque<Instruction*> OUT;
            std::deque<Instruction*> GEN;
            std::deque<Instruction*> KILL;

            std::deque<BasicBlock*> predecessor;
            std::deque<BasicBlock*> successor;
            BasicBlock* bb;
        };        
        static std::map<BasicBlock*, enhancedCFG*> enCFGMap;
  
        // Records all the store that is done on a variable
        struct instHistory {
            bool isIndex;
            std::deque<Instruction*> history;
        };
        static std::map<Value*, instHistory*> indexHist;

        // Record all the pointers according to their base variable
        static std::map<Value*, instHistory*> GEPHist;
        static std::deque<Instruction*> removedGEP;

        void recordHistory(Value* value, std::deque<Instruction*>* hist) {
            std::stack<Value*> stack;

            stack.push(value);
            while(stack.size()!=0) {
                Value* tempValue = stack.top();
                stack.pop();

                if(Instruction::classof(tempValue))
                    hist->push_front(static_cast<Instruction*>(tempValue));

                Instruction* tempInst = static_cast<Instruction*>( tempValue );
                if(tempInst->getOpcode() != Instruction::Load) {
                    for(unsigned i=0;i<tempInst->getNumOperands();i++)
                        stack.push(tempInst->getOperand(i));
                }
            } 
        }

        void recordStoreHistory(Value* value, std::deque<Instruction*>* hist) {
            std::stack<Value*> stack;

            Instruction* store = static_cast<Instruction*>(value);
            stack.push(store->getOperand(0));
            while(stack.size()!=0) {
                Value* tempValue = stack.top();
                stack.pop();

                if(Instruction::classof(tempValue)) {
                    hist->push_front(static_cast<Instruction*>(tempValue));

                    Instruction* tempInst = static_cast<Instruction*>( tempValue );
                    if(tempInst->getOpcode() != Instruction::Load) {
                        for(unsigned i=0;i<tempInst->getNumOperands();i++)
                            stack.push(tempInst->getOperand(i));
                    }
                }
            }
        }        


        Instruction* getGEPLoad(Instruction* inst) {
            // Backward search the index to find the load instruction
            std::stack<Value*> stack;
            stack.push(inst->getOperand( inst->getNumOperands()-1 ));
            while(stack.size()!=0) {
                Value* tempValue = stack.top();
                stack.pop();

                if(Instruction::classof(tempValue)) {
                    Instruction* tempInst = static_cast<Instruction*>( tempValue );
                    if( tempInst->getOpcode()==Instruction::Load )
                        return tempInst;
                    else {
                        for(unsigned i=0;i<tempInst->getNumOperands();i++)
                            stack.push(tempInst->getOperand(i));
                    }
                }
            }
            return NULL;
        }

        void dumpHistory(std::deque<Instruction*>* hist, unsigned nTabs) {
            for(unsigned i=0;i<hist->size();i++) {
                for(unsigned j=0;j<nTabs;j++)
                    errs() << "\t";
                errs() << i << ": ";
                (*hist)[i]->dump();
            }  
        }

        void dumpIndexHistory(std::map<Value*, instHistory*>* map ) {
            errs()<<"dumpIndexHistory...size " << map->size() << "\n";
            int i = 0;
            for(std::map<Value*, instHistory*>::iterator it=map->begin(); it!=map->end();it++) {
                if(it->second->isIndex) {
                    errs() << i << ": ";
                    it->first->dump();
                    dumpHistory(&it->second->history, 1);
                    i++;
                }
            }
        }

        bool identicalValue(Value* left, Value* right) {
            std::deque<Instruction*> leftHist, rightHist;

            recordHistory(left, &leftHist);
            recordHistory(right, &rightHist);

//            dumpHistory(&leftHist, 3);
//            dumpHistory(&rightHist, 4);

            if(leftHist.size()==0&& rightHist.size()==0) {
                if(left->getValueID()==Value::ConstantIntVal && right->getValueID()==Value::ConstantIntVal) {
                    return constIsSame(left, right);
                }
            }

            if(leftHist.size()!=rightHist.size()) {
                return false;
            }
            else {
                for(unsigned i=0;i<leftHist.size();i++) {
                    if(!instIsIdentical(leftHist[i], rightHist[i])) {
                        return false;
                    }
                }
                return true;
            }
        }

        bool instIsIdentical(Instruction* l, Instruction* r) {
            if(l->getOpcode()!=r->getOpcode())
                return false;
            else {
                if(l->getOpcode() ==Instruction::Add || l->getOpcode()==Instruction::Mul ||
                   l->getOpcode() ==Instruction::FAdd || l->getOpcode()==Instruction::FMul ) {
                    if(l->getOperand(0)->getValueID()==Value::ConstantIntVal && r->getOperand(0)->getValueID()==Value::ConstantIntVal) {
                        if( constIsSame(r->getOperand(0), r->getOperand(0)) ) {
                            if(l->getOperand(1)->getValueID()==Value::ConstantIntVal && r->getOperand(1)->getValueID()==Value::ConstantIntVal)
                                return constIsSame(l->getOperand(1), r->getOperand(1));
                            else
                                return instIsIdentical( static_cast<Instruction*>(l->getOperand(1)), static_cast<Instruction*>(r->getOperand(1)));
                        }
                        else
                            return false;
                    }
                    else if(l->getOperand(0)->getValueID()==Value::ConstantIntVal && r->getOperand(1)->getValueID()==Value::ConstantIntVal) {
                        if( constIsSame(r->getOperand(0), r->getOperand(1)) ) {
                            if(l->getOperand(1)->getValueID()==Value::ConstantIntVal && r->getOperand(0)->getValueID()==Value::ConstantIntVal)
                                return constIsSame(l->getOperand(1), r->getOperand(0));
                            else
                                return instIsIdentical(static_cast<Instruction*>(l->getOperand(1)), static_cast<Instruction*>(r->getOperand(0)));
                        }
                        else
                            return false;
                    }
                    else if(l->getOperand(1)->getValueID()==Value::ConstantIntVal && r->getOperand(0)->getValueID()==Value::ConstantIntVal) {
                        if( constIsSame(r->getOperand(1), r->getOperand(0)) ) {
                            if(l->getOperand(0)->getValueID()==Value::ConstantIntVal && r->getOperand(1)->getValueID()==Value::ConstantIntVal)
                                return constIsSame(l->getOperand(0), r->getOperand(1));
                            else
                                return instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(1)));
                        }
                        else
                            return false;

                    }
                    else if(l->getOperand(1)->getValueID()==Value::ConstantIntVal && r->getOperand(1)->getValueID()==Value::ConstantIntVal) {
                        if( constIsSame(r->getOperand(1), r->getOperand(1)) ) {
                            if(l->getOperand(0)->getValueID()==Value::ConstantIntVal && r->getOperand(0)->getValueID()==Value::ConstantIntVal)
                                return constIsSame(l->getOperand(0), r->getOperand(0));
                            else
                                return instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(0)));
                        }
                        else
                            return false;
                    }
                    else {
                        bool case1a = instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(0)));
                        bool case1b = instIsIdentical(static_cast<Instruction*>(l->getOperand(1)), static_cast<Instruction*>(r->getOperand(1)));
                        bool case2a = instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(1)));
                        bool case2b = instIsIdentical(static_cast<Instruction*>(l->getOperand(1)), static_cast<Instruction*>(r->getOperand(0)));
                        return (case1a&&case1b) || (case2a&&case2b);
                    }
                }
                else if( l->getOpcode()==Instruction::Sub || l->getOpcode()==Instruction::FSub ||
                         l->getOpcode()==Instruction::UDiv || l->getOpcode()==Instruction::SDiv || l->getOpcode()==Instruction::FDiv) {
                    if(l->getOperand(0)->getValueID()==Value::ConstantIntVal && r->getOperand(0)->getValueID()==Value::ConstantIntVal) {
                        if( constIsSame(r->getOperand(0), r->getOperand(0)) ) {
                            if(l->getOperand(1)->getValueID()==Value::ConstantIntVal && r->getOperand(1)->getValueID()==Value::ConstantIntVal)
                                return constIsSame(l->getOperand(1), r->getOperand(1));
                            else
                                return instIsIdentical( static_cast<Instruction*>(l->getOperand(1)), static_cast<Instruction*>(r->getOperand(1)));
                        }
                        else
                            return false;
                    }
                    else if(l->getOperand(1)->getValueID()==Value::ConstantIntVal && r->getOperand(1)->getValueID()==Value::ConstantIntVal) {
                        if( constIsSame(r->getOperand(1), r->getOperand(1)) ) {
                            if(l->getOperand(0)->getValueID()==Value::ConstantIntVal && r->getOperand(0)->getValueID()==Value::ConstantIntVal)
                                return constIsSame(l->getOperand(0), r->getOperand(0));
                            else
                                return instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(0)));
                        }
                        else
                            return false;
                    }
                    else {
                        bool case1a = instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(0)));
                        bool case1b = instIsIdentical(static_cast<Instruction*>(l->getOperand(1)), static_cast<Instruction*>(r->getOperand(1)));
                        return (case1a&&case1b);
                    }
                }
                else if(l->getOpcode() == Instruction::Load)
                    return l->getOperand(0)==r->getOperand(0);
                else if(l->getOpcode() == Instruction::SExt || l->getOpcode()==Instruction::ZExt)
                    return instIsIdentical(static_cast<Instruction*>(l->getOperand(0)), static_cast<Instruction*>(r->getOperand(0)));
                else
                    return false;

            }
            return false;
        }

        bool constIsSame(Value* l, Value* r) {
            ConstantInt* leftArg = static_cast<ConstantInt*>(l);
            ConstantInt* rightArg = static_cast<ConstantInt*>(r);
            int64_t leftConst = leftArg->getZExtValue();
            int64_t rightConst = rightArg->getZExtValue();
            return (leftConst==rightConst);
        }     

        bool existStoreForIndex(BasicBlock* bb, Value* inst) {
            for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                if(inst->getOpcode()==Instruction::Store) {
                    if(inst->getOperand(1)==inst)
                        return true;
                }
            }
            return false;
        }

        bool findBasicBlockInQueue(std::deque<BasicBlock*>* queue, BasicBlock* bb) {
            for(unsigned i=0;i<queue->size();i++)
                if((*queue)[i]==bb)
                    return true;
            return false;
        }
 
        bool findInstructionInQueue(std::deque<Instruction*>* queue, Instruction* inst) {
            for(unsigned i=0;i<queue->size();i++)
                if((*queue)[i]==inst)
                    return true;
            return false;
        }

        bool findRemoveInstructionInQueue(std::deque<Instruction*>* queue, Instruction* inst) {
            for(unsigned i=0;i<queue->size();i++) {
                if((*queue)[i]==inst) {
                    queue->erase( queue->begin()+i);
                    return true;
                }
            }
            return false;
        }

        void buildEnhancedCFG(Function& F) {
            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                enhancedCFG* ecfg = new struct enhancedCFG;
                ecfg->bb = bb;

                for(unsigned i=0; i<bb->getTerminator()->getNumSuccessors();i++)
                    ecfg->successor.push_back( bb->getTerminator()->getSuccessor(i) );

                enCFGMap.insert(std::pair<BasicBlock*, enhancedCFG*>(bb, ecfg));
            }

            for(std::map<BasicBlock*, enhancedCFG*>::iterator it=enCFGMap.begin(); it!=enCFGMap.end();it++) {
                enhancedCFG* ecfg = it->second;
                BasicBlock* bb = it->first;

                // Setup successor pointer
                for(unsigned i=0;i<ecfg->successor.size();i++) {
                    std::map<BasicBlock*, enhancedCFG*>::iterator it2 = enCFGMap.find(ecfg->successor[i]);
                    assert(it2!=enCFGMap.end());

                    if( !findBasicBlockInQueue(&it2->second->predecessor, it->first) )
                        it2->second->predecessor.push_back(it->first);
                }

                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    if( inst->getOpcode()==Instruction::Alloca ) {
                        instHistory* ptr = new instHistory;
                        ptr->isIndex = false;
                        if(indexHist.find(inst)!=indexHist.end()) {
#ifdef DEBUG
                            errs() << "WARNING! Alloca instruciton already in indexHist: ";
                            inst->dump();
#endif
                        }
                        indexHist.insert( std::pair<Value*, instHistory*>((Value*)inst, ptr));

                        ptr = new instHistory;
                        ptr->isIndex = false;
                        if(GEPHist.find(inst)!=GEPHist.end()) {
#ifdef DEBUG
                            errs() << "WARNING! Alloca instruciton already in GEPHist: ";
                            inst->dump();
#endif
                        }
                        GEPHist.insert( std::pair<Value*, instHistory*>((Value*)inst, ptr));
                    }
                    else if( inst->getOpcode()==Instruction::Store)
                        it->second->storeList.push_back(inst);

                }
            }

            for(std::map<BasicBlock*, enhancedCFG*>::iterator it=enCFGMap.begin(); it!=enCFGMap.end();it++) {
                enhancedCFG* ecfg = it->second;
                BasicBlock* bb = it->first;

                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    // Record the array access instruction
                    if( inst->getOpcode()==Instruction::GetElementPtr ) {
                        ecfg->checkBounds.push_back(inst);
                        ecfg->GEN.push_back(inst);

                        Instruction* tempInst = getGEPLoad(inst);
                        if(tempInst!=NULL) {
                            ecfg->usedIndex.push_back(tempInst);

                            std::map<Value*, instHistory*>::iterator it = indexHist.find(tempInst->getOperand(0));
                            if(it!=indexHist.end())
                                it->second->isIndex = true;
                            else {
#ifdef DEBUG
                                errs() << "\nWARNING! Can not find instruction in indexHist: ";
                                tempInst->getOperand(0)->dump();
                                dumpIndexHistory(&indexHist);
#endif
                            }

                            // Record a global GEP history
                            std::map<Value*, instHistory*>::iterator it2 = GEPHist.find(tempInst->getOperand(0));
                            if(it2!=GEPHist.end()) {
                                it2->second->isIndex = true;
                                it2->second->history.push_back(inst);
                            }
                        }
                    }
                    // Record if there is a store that modifies a array index variable
                    else if( inst->getOpcode()==Instruction::Store ) {
                        std::map<Value*, instHistory*>::iterator it = indexHist.find(inst->getOperand(1));
                        if(it!=indexHist.end()) 
                            it->second->history.push_back(inst);
                    }
                }
            }
        }

        void analyzeEnCFG(Function& F, bool monotonic) {
            // Formulate GEN       
            for(std::map<BasicBlock*, enhancedCFG*>::iterator it=enCFGMap.begin(); it!=enCFGMap.end(); it++) {
                BasicBlock* bb = it->second->bb;
                for(unsigned i=0;i<it->second->checkBounds.size();i++) {
                    Instruction* ldInst = getGEPLoad(it->second->checkBounds[i]);

                    if(ldInst!=NULL) {
                        if(!existStoreForIndex(bb, ldInst->getOperand(0)) && !findInstructionInQueue(&it->second->GEN, it->second->checkBounds[i])  ) 
                            it->second->GEN.push_back(it->second->checkBounds[i]);
                    }
                }
            }

            // Forumulate KILL
            for(std::map<Value*, instHistory*>::iterator it=indexHist.begin(); it!=indexHist.end();it++) {
                for(unsigned i=0;i<it->second->history.size();i++) {
                    if(monotonic) {
                        if( isKillable(it->second->history[i]) ) {
                            BasicBlock* bb = it->second->history[i]->getParent();
                            std::map<Value*, instHistory*>::iterator it2 = GEPHist.find(it->first);
                            std::map<BasicBlock*, enhancedCFG*>::iterator it3 = enCFGMap.find(bb);

                            assert(it3!=enCFGMap.end());

                            if(it2!=GEPHist.end()) {
                                for(unsigned j=0;j<it2->second->history.size();j++) {
                                    if(bb!=it2->second->history[j]->getParent() && !findInstructionInQueue(&it3->second->KILL, it2->second->history[j]) )
                                        it3->second->KILL.push_back(it2->second->history[j]); 
                                }
                            } 
                            else {
#ifdef DEBUG
                                errs() << "ERROR! A GEP is missing!\n";
#endif
                            }
                        }
                    }
                    else {
                        BasicBlock* bb = it->second->history[i]->getParent();
                        std::map<Value*, instHistory*>::iterator it2 = GEPHist.find(it->first);
                        std::map<BasicBlock*, enhancedCFG*>::iterator it3 = enCFGMap.find(bb);

                        assert(it3!=enCFGMap.end());

                        if(it2!=GEPHist.end()) {
                            for(unsigned j=0;j<it2->second->history.size();j++) {
                                if(bb!=it2->second->history[j]->getParent() && !findInstructionInQueue(&it3->second->KILL, it2->second->history[j]) )
                                    it3->second->KILL.push_back(it2->second->history[j]);
                            }
                        }
                        else {
#ifdef DEBUG
                            errs() << "ERROR! A GEP is missing!\n";
#endif
                        }
                    }
                }
            }

            // Iterate through until converge
            std::stack<BasicBlock*> stack;
            stack.push(F.begin());
            bool modified = false;
            while(!modified) {
                for(Function::iterator bb = F.begin(); bb != F.end(); ++bb) {
                    std::map<BasicBlock*, enhancedCFG*>::iterator it= enCFGMap.find(bb);
                    assert(it!=enCFGMap.end());
                    enhancedCFG* ecfg = it->second;

                    modified = modified || calculateIN(ecfg);
                    modified = modified || calculateOUT(ecfg);
                }
                if(modified)
                    modified = false;
                else
                    break;
            }
        }

        bool isKillable(Instruction* inst) {
            std::deque<Instruction*> hist;

            recordStoreHistory(inst, &hist);

            // Stores a constant
            bool monotonic = true;
            if(hist.size()==0)
                return true;
            else {
                for(unsigned i=0;i<hist.size();i++) {
                    Instruction* inst2 = hist[i];
                    unsigned opcode = inst2->getOpcode();
                    if(opcode==Instruction::Add || 
                       opcode==Instruction::Sub ||
                        opcode==Instruction::Mul ) {
                        if( (inst2->getOperand(0)->getValueID()!=Value::ConstantIntVal) &&
                             inst2->getOperand(1)->getValueID()!=Value::ConstantIntVal) {
                            errs() << "Instruction is not monotonic: ";
                            inst->dump();
                        }
                    }
                    else if(opcode==Instruction::Load) {
                        // Do nothing
                    }
                    else {
                        monotonic = false;
                    }
                }
            } 
            
            return !monotonic;
        }

        void removeGEP() {
            for(std::map<BasicBlock*, enhancedCFG*>::iterator it=enCFGMap.begin(); it!=enCFGMap.end(); it++) {
                for(unsigned i=0;i<it->second->checkBounds.size();i++) {
                    Instruction* gep = it->second->checkBounds[i];

                    for(unsigned j=0;j<it->second->IN.size();j++) {
                        Instruction* in = it->second->IN[j];
             
#ifdef PART3_GLOBAL_VALUE_NUMBERING
                        if( identicalValueGVN(gep->getOperand(gep->getNumOperands()-1), in->getOperand(in->getNumOperands()-1)) ) {
                            if((!findInstructionInQueue(&removedGEP, gep)) && (!findInstructionInQueue(&removedGEP, in))) { 
                                if(!storeToIndex(&it->second->storeList, getGEPLoad(gep))) {
#ifdef PRINT_REMOVE_INFO
                                    errs() << "[globalElimination] Removing check for: " << gep->getParent()->getName() << ", ";
                                    gep->dump(); 
#endif
                                    removedGEP.push_back(gep);
                                }
                            }
                        }
#else   // else for PART3_GLOBAL_VALUE_NUMBERING
                        if( identicalValue(gep->getOperand(gep->getNumOperands()-1), in->getOperand(in->getNumOperands()-1)) ) {
                            if( (!findInstructionInQueue(&removedGEP, gep)) && (!findInstructionInQueue(&removedGEP, in)) ) {
                                if(!storeToIndex(&it->second->storeList, getGEPLoad(gep))) {
#ifdef PRINT_REMOVE_INFO
                                    errs() << "[globalElimination] Removing check for: " << gep->getParent()->getName() << ", ";
                                    gep->dump();
#endif
                                    removedGEP.push_back(gep);
                                }
                            }
                        }
#endif
                    }
                }
            }
        }

        bool storeToIndex(std::deque<Instruction*>* storeList, Instruction* load) {
            if(load==NULL)
                return true;

            for(unsigned i=0;i<storeList->size();i++) {
                if( (*storeList)[i]->getOperand(1)==load->getOperand(0) ) {
                    return true;
                }  
            }
            return false;
        }


        // Return true/false if IN set was modified/unmodified
        bool calculateIN(enhancedCFG* cfg) {
            bool modified = false;
            for(unsigned i=0;i<cfg->predecessor.size();i++) {
                std::map<BasicBlock*, enhancedCFG*>::iterator it=enCFGMap.find(cfg->predecessor[i]);   
                assert(it!=enCFGMap.end());
         
                for(unsigned j=0;j<it->second->OUT.size();j++) {
                    if(!findInstructionInQueue(&cfg->IN, it->second->OUT[j])) {
                        cfg->IN.push_back(it->second->OUT[j]);
                        modified = true;
                    }
                }
            }

            return modified;
        }

        // Return true/false if OUT set was modified/unmodified
        bool calculateOUT(enhancedCFG* cfg) {
            std::deque<Instruction*> tempOut = cfg->IN;
            assert(tempOut.size()==cfg->IN.size());

            // C_IN[B]-C_KILL[B]
            for(unsigned i=0;i<cfg->KILL.size();i++)
                findRemoveInstructionInQueue(&tempOut, cfg->KILL[i]);
    
            // (C_IN[B]-C_KILL[B]) U C_GEN[B]
            for(unsigned i=0;i<cfg->GEN.size();i++) {
                if( !findInstructionInQueue(&tempOut, cfg->GEN[i]) )
                    tempOut.push_back(cfg->GEN[i]);
            }
                    
            if(tempOut!=cfg->OUT) {
                cfg->OUT = tempOut;
                return true;
            }
            return false;
        }        
    
        bool hasElement(enhancedCFG* cfg) {
            if( cfg->checkBounds.size() != 0 || cfg->usedIndex.size() != 0   ||
                cfg->IN.size() != 0          || cfg->OUT.size() != 0         || 
                cfg->GEN.size() != 0         || cfg->KILL.size() != 0 )
                return true;
            else
                return false;
        }

        void dumpEnhancedCFG(std::map<BasicBlock*, enhancedCFG*>* map) {
            int i=0;
            for(std::map<BasicBlock*, enhancedCFG*>::iterator it = map->begin(); it!=map->end(); it++) {
                if( hasElement(it->second) ) {
                    errs() << "[Basic block " << i << ": " << it->first->getName() << "]\n";
                    
                    errs() << "\tpredecessor:\n"; 
                    for(unsigned j=0;j<it->second->predecessor.size();j++)
                        errs() << "\t\t" << j << ": " << it->second->predecessor[j]->getName() << "\n";
                    errs() << "\tsuccessor:\n";   
                    for(unsigned j=0;j<it->second->successor.size();j++)
                        errs() << "\t\t" << j << ": " << it->second->successor[j]->getName() << "\n";

                    errs() << "\tcheck bounds:\n";  dumpHistory(&(it->second->checkBounds), 2);
                    errs() << "\tused index:\n";    dumpHistory(&(it->second->usedIndex), 2);
                    errs() << "\tstore list:\n";    dumpHistory(&(it->second->storeList), 2);
                    
                    errs() << "\tGEN:\n";           dumpHistory(&(it->second->GEN), 2);
                    errs() << "\tKILL:\n";          dumpHistory(&(it->second->KILL), 2);
                    errs() << "\tIN:\n";            dumpHistory(&(it->second->IN), 2);
                    errs() << "\tOUT:\n";           dumpHistory(&(it->second->OUT), 2);

                    i++;
                }
            }
        }




        /**********************************/
        /* Functions for loop propagation */
        /**********************************/
        static std::map<BasicBlock*, std::deque<BasicBlock*>*> dominatorSetMap;
        static std::map<BasicBlock*, std::deque<BasicBlock*>*> dominatesSetMap;

        void dumpDomSetMap(std::map<BasicBlock*, std::deque<BasicBlock*>*>* map) {
            for(std::map<BasicBlock*, std::deque<BasicBlock*>*>::iterator it=map->begin(); it!=map->end();it++) {
                errs() << "Basic block: " << it->first->getName() << "\n";
                for(unsigned i=0;i<it->second->size();i++) 
                    errs() << "\t" << i << ": " << (*it->second)[i]->getName() << "\n";
            }
        }

        void generateDomSet(Function& F, DominatorTree &domTree) {
            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb) {
                dominatorSetMap.insert( std::pair<BasicBlock*, std::deque<BasicBlock*>*>(bb, new std::deque<BasicBlock*>) );
                dominatesSetMap.insert( std::pair<BasicBlock*, std::deque<BasicBlock*>*>(bb, new std::deque<BasicBlock*>) );
            }

            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                std::map<BasicBlock*, std::deque<BasicBlock*>*>:: iterator it = dominatorSetMap.find(bb);
                assert(it!=dominatorSetMap.end());
                for(Function::iterator bb2 = F.begin(); bb2 != F.end(); ++bb2){
                    if(domTree.dominates(bb2->begin(), bb->begin())) {
                        it->second->push_back(bb2);

                        std::map<BasicBlock*, std::deque<BasicBlock*>*>:: iterator it2 = dominatesSetMap.find(bb2);
                        assert(it2!=dominatesSetMap.end());

                        it2->second->push_back(bb);
                    }
                }
            }
        }

        void moveGEP(Instruction* GEP, Instruction* insertPoint) {
            std::stack<Value*> stack;
            std::deque<Instruction*> hist;

            hist.push_front(GEP);

            for(unsigned i=0;i<GEP->getNumOperands();i++) {
                if(!AllocaInst::classof(GEP->getOperand(i)))
                    stack.push(GEP->getOperand(i));
            }

            while(stack.size()!=0) {
                Value* tempValue = stack.top();
                stack.pop();

                if(Instruction::classof(tempValue)) {
                    Instruction* tempInst = static_cast<Instruction*>( tempValue );
                    if(tempInst->getOpcode() != Instruction::Load) {
                        for(unsigned i=0;i<tempInst->getNumOperands();i++)
                            stack.push(tempInst->getOperand(i));
                    }

                    hist.push_front(tempInst);
                }
            }

#ifdef DEBUG
            errs() <<"Moving the following instructions to: ";
            insertPoint->dump();
#endif
            for(unsigned i=0;i<hist.size();i++) {
#ifdef DEBUG
                errs() <<"\t"<<i<<": "; hist[i]->dump();
#endif
                hist[i]->moveBefore(insertPoint);
            }
        }

        void executeLoopPropagation( Function &F, LoopInfo &loopInfo ) {
            bool unModified = true;

            enCFGMap.clear();
            indexHist.clear();
            GEPHist.clear();

            buildEnhancedCFG(F);
            analyzeEnCFG(F, false); // false means that does not enable monotonic check

            while(unModified) { 
                for(std::map<BasicBlock*, enhancedCFG*>::iterator it=enCFGMap.begin(); it!=enCFGMap.end();it++) {
                    BasicBlock* bb = it->first;
                    if( loopInfo.getLoopDepth(bb) !=0 && it->second->checkBounds.size()!=0) {
                        for(unsigned i=0;i<it->second->checkBounds.size();i++) {
                            Instruction* inst = it->second->checkBounds[i];
                            if(findInstructionInQueue(&it->second->IN, inst) && aliveIndex(inst) ) {
                                Loop* loop = loopInfo.getLoopFor(bb);
                                BasicBlock* head = loop->getHeader();

                                std::map<BasicBlock*, enhancedCFG*>::iterator it2 = enCFGMap.find(head);
                                assert(it2!=enCFGMap.end());
                                if(it2->second->predecessor.size()!=0) {

                                    BasicBlock* preHeadBB = getLoopHeadPredBB( &it2->second->predecessor, loopInfo);
                                    Instruction* insertPoint = preHeadBB->getTerminator();                                    

                                    if(preHeadBB!=bb) {
#ifdef PRINT_REMOVE_INFO
                                        errs() << "[LoopPropagation] Move \n" << bb->getName() << ": ";
                                        inst->dump();
                                        errs() << "\t-> " << preHeadBB->getName() << ": ";
                                        insertPoint->dump();     
                                        errs() << "";                  
#endif
                                        moveGEP(inst, insertPoint);
                                        unModified = false;
                                    }
                                }
                                else {
#ifdef DEBUG
                                    errs() << "ERROR! " << bb->getName() << " has no predecessor!\n";
#endif
                                }
                            }
                        }
                    }
                }
                if(!unModified) {
                    enCFGMap.clear();
                    indexHist.clear();
                    GEPHist.clear();

                    buildEnhancedCFG(F);
                    analyzeEnCFG(F, false); // false means that does not enable monotonic check
                }
                unModified = !unModified;
            }
        }


        BasicBlock*  getLoopHeadPredBB(std::deque<BasicBlock*>* preds, LoopInfo& loopInfo) {
            if(preds->size()==0)
                return NULL;
            else if(preds->size()==1)
                return (*preds)[0];
            else {
                BasicBlock* prev = (*preds)[0];
                for(unsigned i=1;i<preds->size();i++) {
                    if( loopInfo.getLoopDepth( (*preds)[i] ) < loopInfo.getLoopDepth(prev) )
                        prev = (*preds)[i];
                }
                return prev;

            }
        }
        
        bool aliveIndex(Instruction* inst) {
            Instruction* loadInst = getGEPLoad(inst);

            if(loadInst!=NULL) {
                BasicBlock* parent = inst->getParent();

                for(BasicBlock::iterator tempInst = parent->begin(); tempInst != parent->end(); ++tempInst) {
                    if(tempInst->getOpcode()==Instruction::Store) {
                        if(tempInst->getOperand(1) == loadInst->getOperand(0)) {
                            return false;
                        }
                    }
                }
            }
            else
                return false;
            return true;
        }
        
        // This function takes an instruction and it's bounds, and checks if it has been subsumed in this basic block.
        // If it has been subsumed, the instruction is added to the delete set.
        // If it hasn't been subsumed, either the existing range is expanded, or a new entry is added to the reference map.
        //
        // MODIFIES: ref_gep_map, local_opt_del_set
        
        void update_local_del_set(Instruction* inst, Value * array_base, int64_t lb, int64_t ub, std::map<Value*, std::pair<int,int> >& ref_gep_map, std::set<Instruction*>& local_opt_del_set ){
            std::map<Value*, std::pair<int,int> >::iterator gep_map_it;
            gep_map_it = ref_gep_map.find(array_base);
            if (gep_map_it != ref_gep_map.end()){

                // A similar check was made earlier. Check if our boundaries are subsumed
                if (gep_map_it -> second.first <= lb && gep_map_it -> second.second >= ub){
                    // Subsumed. So add this instruction to the delete list
#ifdef PRINT_REMOVE_INFO
                    errs() << "Subsumed Check for " << ub << " in Instruction: \n";
                    inst->dump(); 
#endif
                    local_opt_del_set.insert(inst); 
                } else{
                    // Not subsumed. So extend the range of the existing entry.

#ifdef DEBUG
                    errs() << "Expanded check with " << ub << " for instruction: \n";
                    inst->dump(); 
#endif
                    if (lb < gep_map_it -> second.first) gep_map_it -> second.first = lb;
                    if (ub > gep_map_it -> second.second) gep_map_it -> second.second = ub;
                }
            }else{
#ifdef DEBUG
                errs() << "Inserted Check for " << ub << " because of instruction: \n";
                inst->dump(); 
                // Insert this Value* in the ref map
#endif
                ref_gep_map[array_base] = std::pair<int,int>(lb,ub); 
            }

        }
        
        void do_local_optimizations (Function &F,  std::set<Instruction*>& local_opt_del_set){
#ifdef PART2_LOCAL_ELIMINATION
            errs() << "\n*** Start local elimination ***\n";

            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                // Ref Map for existing checks. One Map per basic block.
                // Key is the Value* of the array base. The pair is a pair of low and high bounds already checked
                std::map<Value*, std::pair<int,int> > ref_gep_map;
                // Key is the Value * of the array base. The vale is a set of variables that have been used to index.
                std::map<Value*, std::set<Value*> > ref_gep_operand_map;

                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    if( inst->getOpcode()==Instruction::GetElementPtr ) {
                        GetElementPtrInst *GEP = static_cast<GetElementPtrInst*>( (Instruction*)inst);
                        unsigned num_gep_operands = GEP -> getNumOperands();
                        std::map<Value*, ArrayInfo*>::iterator it = arrayMap.find(GEP->getPointerOperand());
                        if(it!=arrayMap.end()) { // Array indexed directly
                            num_gep_operands = GEP -> getNumOperands();
                            std::map<Value*, std::pair<int,int> >::iterator gep_map_it;
                            // Array indexed with a constant integer
                            if ( num_gep_operands == 3 ){
                                if(isa<ConstantInt>(GEP -> getOperand(2))){
                                    ConstantInt* consUB = cast<ConstantInt>(GEP -> getOperand(2));
                                    int64_t ub = consUB->getSExtValue();
                                    int64_t lb = 0;

                                    update_local_del_set(inst, it->first , lb, ub, ref_gep_map, local_opt_del_set );
                                }else{
                                    // Array indexed with a variable 
                                    std::map<Value*, std::set<Value*> >::iterator ref_gep_operand_map_it = ref_gep_operand_map.find(it->first);
                                    if (ref_gep_operand_map_it != ref_gep_operand_map.end()){
                                        std::set<Value *>::iterator value_set_it;

                                        bool hit = false;
                                        for (value_set_it = ref_gep_operand_map_it->second.begin(); value_set_it != ref_gep_operand_map_it->second.end(); ++value_set_it ){
                                            if (identicalValue(*value_set_it, GEP ->getOperand (2))){

                                                // We got a hit.
                                                hit =  true;
                                                // Already encountered this variable before for this array. Add the ins to the delete set.
                                                local_opt_del_set.insert(inst);
#ifdef PRINT_REMOVE_INFO
                                                errs() << "Removed redundant check in instruction: ";
                                                inst->dump(); 
#endif
                                                break; 
                                            }
                                        }

                                        if(!hit){
                                            // Encountered this array base before, but didn't index with this variable. Insert it
                                            // errs() << "KEY Existed. Inserting Value \n";
                                            // GEP->getOperand(2)->dump();
                                            ref_gep_operand_map_it->second.insert(GEP ->getOperand(2));
                                        }

                                    }else{
                                        // Didn't encounter this array base before
                                        // However, we could've encountered the same index variable for a different array whose range is more restrictive.
                                        // Check for that

                                        bool hit = false;
                                        if(it->second->top_limit >= 1){
                                            std::map<Value*, std::set<Value*> >::iterator ref_gep_operand_map_it;
                                            for(ref_gep_operand_map_it = ref_gep_operand_map.begin(); ref_gep_operand_map_it != ref_gep_operand_map.end(); ++ref_gep_operand_map_it) {
                                                std::map<Value*, ArrayInfo*>::iterator candidate_it;
                                                candidate_it = arrayMap.find(ref_gep_operand_map_it -> first);
                                                if (candidate_it != arrayMap.end() && candidate_it->second->top_limit >=1 && candidate_it->second->top_limit <= it->second->top_limit){
                                                    //This array is a possible candidate.
                                                    std::set<Value *>::iterator value_set_it;

                                                    for (value_set_it = ref_gep_operand_map_it->second.begin(); value_set_it != ref_gep_operand_map_it->second.end(); ++value_set_it ){
                                                        if (identicalValue(*value_set_it, GEP ->getOperand (2))){

                                                            // We got a hit.
                                                            hit =  true;
                                                            // Already encountered this variable before for this array. Add the ins to the delete set.
                                                            local_opt_del_set.insert(inst);
#ifdef PRINT_REMOVE_INFO
                                                            errs() << "Removed redundant check in instruction: ";
                                                            inst->dump(); 
#endif
                                                            break; 
                                                        }
                                                    }        
                                                } 

                                            }
                                        }
                                        // errs() << "Inserted KEY VALUE\n";  
                                        // it->first->dump();
                                        // GEP->getOperand(2)->dump();
                                        if(!hit) {
                                            ref_gep_operand_map[it->first].insert(GEP -> getOperand(2));
                                        }
                                    } 
                                }
                            }else{
#ifdef DEBUG
                                errs() << "WARNING 0! Haven't considered this case!\n";
#endif
                            }
                        } else { // Pointer access
                            Instruction* tempInst = static_cast<Instruction*>( GEP->getPointerOperand() );

                            if( tempInst->getOpcode()==Instruction::Load || tempInst->getOpcode()==Instruction::GetElementPtr ) {
                                it = arrayMap.find( tempInst->getOperand(0) );
                                if( it!=arrayMap.end() ){
                                    num_gep_operands = GEP -> getNumOperands();
                                    if ( num_gep_operands == 2 ){
                                        if(isa<ConstantInt>(GEP -> getOperand(1))){
                                            ConstantInt* consUB = cast<ConstantInt>(GEP -> getOperand(1));
                                            int64_t ub = consUB->getSExtValue();
                                            int64_t lb = 0;
                                            update_local_del_set(inst, it->first , lb, ub, ref_gep_map, local_opt_del_set );
                                        }else{
                                            // Pointer indexed with a variable 
                                            std::map<Value*, std::set<Value*> >::iterator ref_gep_operand_map_it = ref_gep_operand_map.find(it->first);
                                            if (ref_gep_operand_map_it != ref_gep_operand_map.end()){
                                                std::set<Value *>::iterator value_set_it;

                                                bool hit = false;
                                                for (value_set_it = ref_gep_operand_map_it->second.begin(); value_set_it != ref_gep_operand_map_it->second.end(); ++value_set_it ){
                                                    if (identicalValue(*value_set_it, GEP ->getOperand (1))){

                                                        // We got a hit.
                                                        hit =  true;
                                                        // Already encountered this variable before. Add the ins to the delete set.
                                                        local_opt_del_set.insert(inst);
#ifdef PRINT_REMOVE_INFO
                                                        errs() << "Removed redundant check \n";
                                                        inst->dump(); 
#endif
                                                        break; 
                                                    }
                                                }

                                                if(!hit){
                                                    // Encountered this array base before, but didn't index with this variable. Insert it
                                                    // errs() << "KEY Existed. Inserting Value \n";
                                                    // GEP->getOperand(2)->dump();
                                                    ref_gep_operand_map_it->second.insert(GEP ->getOperand(1));
                                                }

                                            }else{
                                                //Didn't encounter this array base before
                                                // However, we could've encountered the same index variable for a different array whose range is more restrictive.
                                                // Check for that

                                                bool hit = false;
                                                if(it->second->top_limit >= 1){
                                                    std::map<Value*, std::set<Value*> >::iterator ref_gep_operand_map_it;
                                                    for(ref_gep_operand_map_it = ref_gep_operand_map.begin(); ref_gep_operand_map_it != ref_gep_operand_map.end(); ++ref_gep_operand_map_it) {
                                                        std::map<Value*, ArrayInfo*>::iterator candidate_it;
                                                        candidate_it = arrayMap.find(ref_gep_operand_map_it -> first);
                                                        if (candidate_it != arrayMap.end() && candidate_it->second->top_limit >=1 && candidate_it->second->top_limit <= it->second->top_limit){
                                                            //This array is a possible candidate.
                                                            std::set<Value *>::iterator value_set_it;

                                                            for (value_set_it = ref_gep_operand_map_it->second.begin(); value_set_it != ref_gep_operand_map_it->second.end(); ++value_set_it ){
                                                                if (identicalValue(*value_set_it, GEP ->getOperand (1))){

                                                                    // We got a hit.
                                                                    hit =  true;
                                                                    // Already encountered this variable before for this array. Add the ins to the delete set.
                                                                    local_opt_del_set.insert(inst);
#ifdef PRINT_REMOVE_INFO
                                                                    errs() << "Removed redundant check in instruction: ";
                                                                    inst->dump(); 
#endif
                                                                    break; 
                                                                }
                                                            }        
                                                        } 

                                                    }
                                                }
                                                // errs() << "Inserted KEY VALUE\n";  
                                                // it->first->dump();
                                                // GEP->getOperand(2)->dump();
                                                if(!hit){ 

                                                    ref_gep_operand_map[it->first].insert(GEP -> getOperand(1));
                                                }
                                            }
                                        }

                                    }else{
#ifdef DEBUG
                                        errs() << "WARNING 1! Haven't considered this case!\n";
#endif
                                    }
                                }
                                else{ 
#ifdef DEBUG
                                    errs() << "WARNING 2! Haven't considered this case! " << GEP->getParent()->getName() << ": ";
                                    GEP->dump();
#endif
                                }
                            }

                        }
                    }
                }
            }
#endif
        }


        /****************************************/
        /* Functions for global value numbering */
        /****************************************/
        static std::map<unsigned, std::deque<Value*>*> congruMap;
        static std::map<Value*, unsigned> reverseCongruMap;

        void initGVNPartition(Function& F) {
            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    unsigned opcode = inst->getOpcode();

                    if(opcode!=Instruction::Ret && opcode!=Instruction::Br && opcode!=Instruction::Call) {
                        std::map<unsigned, std::deque<Value*>*>::iterator it = congruMap.find(opcode);

                        if(it==congruMap.end()) {
                            std::deque<Value*>* ptr = new std::deque<Value*>;
                            ptr->push_back(inst);
                            congruMap.insert( std::pair<unsigned, std::deque<Value*>*>(opcode, ptr));
                        }
                        else
                            it->second->push_back(inst);
                   
                        for(unsigned i=0;i<inst->getNumOperands();i++) {
                            Value* value = inst->getOperand(i);
                            unsigned valueID = value->getValueID();

                            // Only record constant value now
                            if(valueID>=Value::ConstantExprVal && valueID<=Value::ConstantPointerNullVal) {
                                std::map<Value*, unsigned>::iterator it2 = reverseCongruMap.find(value);
                                if(it2==reverseCongruMap.end()) {
                                    
                                    if(valueID==Value::ConstantIntVal) {
                                        valueID = findConstantNumber(value);
                                        if(valueID == 0)
                                            valueID = findUniqueNumber();
                                    }

                                    std::map<unsigned, std::deque<Value*>*>::iterator it3 = congruMap.find(valueID);
                                    if(it3==congruMap.end()) {
                                        std::deque<Value*>* ptr = new std::deque<Value*>;
                                        ptr->push_back(value);
                
                                       congruMap.insert( std::pair<unsigned, std::deque<Value*>*>(valueID, ptr));
                                    }
                                    else 
                                        it3->second->push_back(value);
                                    reverseCongruMap.insert( std::pair<Value*, unsigned>(value, valueID) );
                                }
                            }
                        }
 
                        reverseCongruMap.insert( std::pair<Value*, unsigned>(inst, opcode) );
                    }
                }
            }
        }

        // This implements "Optimistic value-numbering" by assuming all elements are in the same set, and the split each item into separate sets
        void optValueNumbering() {
            std::map<unsigned, std::deque<Value*>*> worklist;     
            worklist = congruMap;

            while(!worklist.empty()) {
                std::map<unsigned, std::deque<Value*>*>::iterator it = worklist.begin();
                std::map<unsigned, std::deque<Value*>*> tempCongruMap = congruMap;
                for(std::map<unsigned, std::deque<Value*>*>::iterator it2=tempCongruMap.begin();it2!=tempCongruMap.end();it2++) {
                    if( properlySplit(it2->second, it->first) && (it->first!=it2->first) ) {
                        divideClass(it2, it, &worklist); 
                    }
                }

                worklist.erase(it);
            }
        }

        void divideClass(std::map<unsigned, std::deque<Value*>*>::iterator splitee, 
                         std::map<unsigned, std::deque<Value*>*>::iterator spliter, 
                         std::map<unsigned, std::deque<Value*>*>* worklist ) {
            unsigned numOperands = static_cast<Instruction*>((*(splitee->second))[0])->getNumOperands();
            // Create in/out set
            std::deque<Value*>* inSet[3];
            std::deque<Value*>* outSet[3];
            for(unsigned i=0;i<3;i++) {
                inSet[i] = new std::deque<Value*>;
                outSet[i] = new std::deque<Value*>;
            }

            for(unsigned p=0;p<numOperands;p++) {
                for(unsigned i=0;i<splitee->second->size();i++) {
                    if(Instruction::classof( (*(splitee->second))[i] )) {
                        Instruction* inst = static_cast<Instruction*>((*(splitee->second))[i]);

                        if(p<inst->getNumOperands()) {
                            Value* instOperand = inst->getOperand(p);

                            std::map<Value*, unsigned>::iterator it = reverseCongruMap.find(instOperand);
                            if(it!=reverseCongruMap.end()) {
                                if(it->second==spliter->first)
                                    inSet[p]->push_back(inst);
                                else
                                    outSet[p]->push_back(inst);
                            }
                        }
                        else
                            outSet[p]->push_back(inst);
                    }
                }
            }

            // Remove old class and create new class
            // NOTE: splitee is from congruMap, and spliter is from worklist
            std::map<unsigned, std::deque<Value*>*>::iterator itt = worklist->find(splitee->first);
            if(itt!=worklist->end())
                worklist->erase(itt);
            itt = congruMap.find(splitee->first);
            assert(itt!=congruMap.end());
            congruMap.erase(itt);

            for(unsigned i=0;i<numOperands;i++) {
                if((inSet[i]->size()!=0) && (outSet[i]->size()!=0)) { 
                    unsigned newID = findUniqueNumber();
                    worklist->insert( std::pair<unsigned, std::deque<Value*>*>(newID, inSet[i]) ); 
                    congruMap.insert( std::pair<unsigned, std::deque<Value*>*>(newID, inSet[i]) );
                    updateReverseCongruMap(inSet[i], newID);

                    newID = findUniqueNumber();
                    worklist->insert( std::pair<unsigned, std::deque<Value*>*>(newID, outSet[i]) );
                    congruMap.insert( std::pair<unsigned, std::deque<Value*>*>(newID, outSet[i]) );
                    updateReverseCongruMap(outSet[i], newID);

                    break;
                }
            }
        }

        void updateReverseCongruMap(std::deque<Value*>* queue, unsigned newID) {
            for(unsigned i=0;i<queue->size();i++) {
                std::map<Value*, unsigned>::iterator it = reverseCongruMap.find( (*queue)[i] );
                if(it!=reverseCongruMap.end())
                    it->second = newID;
                else {
                    errs() << "ERROR! Cannot find entry in reverseCongruMap!: ";
                    (*queue)[i]->dump();
                }
            }
        }

        bool properlySplit(std::deque<Value*>* splitee, unsigned spliter) {
            assert(splitee->size()!=0);
            unsigned numOperands;

            if(Instruction::classof( (*splitee)[0] ) )
                numOperands = static_cast<Instruction*>((*splitee)[0])->getNumOperands();
            else 
                return false;

            assert(numOperands<=3);
            std::deque<Value*> inSet[3];
            std::deque<Value*> outSet[3];
            for(unsigned p=0;p<numOperands;p++) {
                for(unsigned i=0;i<splitee->size();i++) {
                    if(Instruction::classof( (*splitee)[i] )) {
                        Instruction* inst = static_cast<Instruction*>((*splitee)[i]);
                        if(p<inst->getNumOperands()) {
                            Value* instOperand = inst->getOperand(p);
                            std::map<Value*, unsigned>::iterator it = reverseCongruMap.find(instOperand);
                            
                            if(it!=reverseCongruMap.end()) {
                                if(it->second==spliter)
                                    inSet[p].push_back(inst);
                                else
                                    outSet[p].push_back(inst);
                            }
                        }
                        else {
                            outSet[p].push_back(inst);
                        }
                    }
                }  
            }

            for(unsigned i=0;i<numOperands;i++) {
                if((inSet[i].size()!=0) && (outSet[i].size()!=0))
                    return true;
            }

            return false;
        }

        unsigned findConstantNumber(Value* value) {
            for(std::map<unsigned, std::deque<Value*>*>::iterator it=congruMap.begin();it!=congruMap.end();it++) {
                if(it->first>100)  {
                    if( (*it->second)[0]==value )
                        return it->first;
                }    
            }
            return 0;
        }        

        static unsigned uniqueNumber;
        unsigned findUniqueNumber() {
            unsigned number=uniqueNumber;
            uniqueNumber++;
            while(1) {
                std::map<unsigned, std::deque<Value*>*>::iterator it = congruMap.find(number);
                if(it==congruMap.end())
                    return number;
                else
                    number++;
            }
        }

        void dumpCongruMap() {
            for(std::map<unsigned, std::deque<Value*>*>::iterator it=congruMap.begin(); it!=congruMap.end();it++) {
                errs() << "[Group " << it->first << "]\n";
                for(std::deque<Value*>::iterator it2=it->second->begin(); it2!=it->second->end();it2++) {
                    errs() <<"\t";
                    if(Instruction::classof( (*it2)) ) {
                        Instruction* inst = static_cast<Instruction*>(*it2);
                        errs() <<": "<< inst->getParent()->getName() << ", ";
                    }
                    (*it2)->dump();
                }
            }
        }

        void dumpReverseCongruMap() {
            for(std::map<Value*, unsigned>::iterator it=reverseCongruMap.begin(); it!=reverseCongruMap.end();it++) {
                errs() << it->second << ":\t";
                it->first->dump();
            }
        }

        bool identicalValueGVN(Value* left, Value* right) {
            std::map<Value*, unsigned>::iterator it = reverseCongruMap.find(left);
            std::map<Value*, unsigned>::iterator it2 = reverseCongruMap.find(right);

            return it->second==it2->second;
        }

        bool instIsIdenticalGVN(Value* l, Value* r) {
            std::map<Value*, unsigned>::iterator it = reverseCongruMap.find(l);
            std::map<Value*, unsigned>::iterator it2 = reverseCongruMap.find(r);

            return it->second==it2->second;
        }


        /********************************/
        /* Main functions for llvm pass */
        /********************************/
        Project() : FunctionPass(ID) {}
        void globalValueNumbering(Function& F) {
#ifdef PART3_GLOBAL_VALUE_NUMBERING
            errs() << "\n*** Start global value numbering ***\n";
            congruMap.clear();
            reverseCongruMap.clear();

            initGVNPartition(F);
            optValueNumbering();
            optValueNumbering();

            #ifdef DEBUG
            errs() << "\n=== Congruence map ===\n"; dumpCongruMap();
            errs() << "\n=== Reverse congruence map ===\n"; dumpReverseCongruMap();
            #endif
#endif
        }

        void globalElimination(Function& F) {
#ifdef PART2_GLOBAL_ELIMINATION
            errs() << "\n*** Start global elimination ***\n";
            // [Global Elimination]
            // Initialization 
            enCFGMap.clear();
            indexHist.clear();
            GEPHist.clear();
            removedGEP.clear();

            // Initialize the necessary meta data 
            buildEnhancedCFG(F);
            // Create IN/OUT/GEN/KILL set and interatively determine the unnecessary checks
            analyzeEnCFG(F, false);
            // Create the removedGEP set
            removeGEP();

            // Debug print
            #ifdef DEBUG
            errs() << "\n=== removed GEP ===\n";  dumpHistory(&removedGEP, 1);
            errs() << "\n=== Array map ===\n";      dumpArrayInfoMap(&arrayMap);
            errs() << "\n=== Enchanged CFG ===\n";  dumpEnhancedCFG(&enCFGMap);
            errs() << "\n=== Index history ===\n";  dumpIndexHistory(&indexHist);
            errs() << "\n=== GEP history ===\n";    dumpIndexHistory(&GEPHist);
            #endif
#endif
        }

        void loopPropagation(Function& F) {
#ifdef PART2_LOOP_PROPAGATION
            errs() << "\n*** Start loop propagation ***\n";
            // [Loop propagation]
            // Initialization
            LoopInfo &loopInfo = getAnalysis<LoopInfo>();

#ifdef LLVM_3_4
            DominatorTree &domTree = getAnalysis<DominatorTree>();
#else
            DominatorTreeWrapperPass &dominator = getAnalysis<DominatorTreeWrapperPass>();
            DominatorTree &domTree = dominator.getDomTree();
#endif
            dominatorSetMap.clear();
            dominatesSetMap.clear();

            generateDomSet(F, domTree);
            executeLoopPropagation(F, loopInfo);

            // Debug pint
            #ifdef DEBUG
            errs() << "\n=== Dominator set ===\n"; dumpDomSetMap(&dominatorSetMap);
            errs() << "\n=== Dominates set ===\n"; dumpDomSetMap(&dominatesSetMap);
            #endif
#endif
        }

        virtual bool doInitialization(Module &M) {
            errs() << "\n[doInitialization]\n";
            return false;
        }

        virtual bool runOnFunction(Function &F) {
            errs() << "\n=============================================\n";
            errs() << "[ runOnFunction - " << F.getName() << " ]\n";
            errs() << "=============================================\n";


            //F.viewCFG();

            // Create meta data for instructions
            TargetLibraryInfo &tlInfo = getAnalysis<TargetLibraryInfo>();
            DataLayout &dLayout = getAnalysis<DataLayout>();
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

            globalValueNumbering(F);

            // Del GEP set. One set for the entire function
            std::set<Instruction*> local_opt_del_set;

            do_local_optimizations (F, local_opt_del_set);

            globalElimination(F);

            loopPropagation(F);

            // Insert bound checks
            errs() << "\n*** Start inserting bound checks ***\n";
            long insertedChecks = 0;
            for(Function::iterator bb = F.begin(); bb != F.end(); ++bb){
                for(BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    if( inst->getOpcode()==Instruction::GetElementPtr ) { // Check for pointer element access

                        Instruction * inst_copy = inst;

#if defined(PART2_LOCAL_ELIMINATION)
                        if (local_opt_del_set.count(inst)) inst_copy = NULL;
#endif

#if defined(PART2_GLOBAL_ELIMINATION) || defined(PART2_LOOP_PROPAGATION)
                        if( findInstructionInQueue(&removedGEP, inst)) inst_copy = NULL;
#endif

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


        virtual bool doFinalization(Module &M) {
            errs() << "\n[doFinalization]\n";

            return false;
        }

        virtual void getAnalysisUsage(AnalysisUsage &AU) const {
            AU.setPreservesAll();
            AU.addRequired<TargetLibraryInfo>();
            AU.addRequired<DataLayout>();
            AU.addRequired<LoopInfo>();
#ifdef LLVM_3_4
            AU.addRequired<DominatorTree>();
#else
            AU.addRequired<DominatorTreeWrapperPass>();
#endif
            AU.addRequired<DominanceFrontier>();
            AU.addRequired<PostDominatorTree>();
        }

    };  // end of struct Project : public FunctionPass 
}

// Needs to declar static variables
char Project::ID = 0;
std::map<Value*,  ArrayInfo*> Project::arrayMap;

// Static variables for Part2 - Global eliminate
std::map<BasicBlock*, Project::enhancedCFG*> Project::enCFGMap;
std::map<Value*, Project::instHistory*> Project::indexHist;
std::map<Value*, Project::instHistory*> Project::GEPHist;
std::deque<Instruction*> Project::removedGEP;
// Static variables for Part2 - Loop propagation
std::map<BasicBlock*, std::deque<BasicBlock*>*> Project::dominatorSetMap;
std::map<BasicBlock*, std::deque<BasicBlock*>*> Project::dominatesSetMap;
// Static variables for Part3 - Global value numbering
std::map<unsigned, std::deque<Value*>*> Project::congruMap;
std::map<Value*, unsigned> Project::reverseCongruMap;
unsigned Project::uniqueNumber = 100;


// Register Project pass command
static RegisterPass<Project> X("project", "project tests");
