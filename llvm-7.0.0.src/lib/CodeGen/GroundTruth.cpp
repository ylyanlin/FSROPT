#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/GroundTruth.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/InitializePasses.h"
#include "llvm/IR/Value.h"
//#include "llvm/DebugInfo.h"
using namespace llvm;

//STATISTIC(NumCFIIndirectCalls,
          //"Number of indirect call sites rewritten by the CFI pass");

char GroundTruth::ID = 0;
INITIALIZE_PASS_BEGIN(GroundTruth, "g-truth",
                      "g-truth", true, true)

INITIALIZE_PASS_END(GroundTruth, "g-truth",
                    "g-truth", true, true)
                    

FunctionPass *llvm::createGroundTruthPass() {
  return new GroundTruth();
}  




// Checks to see if a given CallSite is making an indirect call, including
// cases where the indirect call is made through a bitcast.
static bool isIndirectCall(CallSite &CS) {
  if (CS.getCalledFunction())
    return false;

  // Check the value to see if it is merely a bitcast of a function. In
  // this case, it will translate to a direct function call in the resulting
  // assembly, so we won't treat it as an indirect call here.
  const Value *V = CS.getCalledValue();
  if (!V)
	return false;
  if (isa<Function>(V) || isa<Constant>(V))
       return false;
  if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
    return !(CE->isCast() && isa<Function>(CE->getOperand(0)));
  }

  // Otherwise, since we know it's a call, it must be an indirect call
  return true;
  
}

bool GroundTruth::doInitialization(Module &M) 
{
	DL = &M.getDataLayout();


	IntPtrTy = DL->getIntPtrType(M.getContext());
	Int32Ty = Type::getInt32Ty(M.getContext());
	Int8Ty = Type::getInt8Ty(M.getContext());
	Int64Ty = Type::getInt64Ty(M.getContext());
	Int128Ty = Type::getInt128Ty(M.getContext());
	Int16Ty = Type::getInt16Ty(M.getContext());
	BoolTy = Type::getInt1Ty(M.getContext());
	
	
	return false;
}       


GroundTruth::GroundTruth()
    : FunctionPass(ID) {
  initializeGroundTruthPass(*PassRegistry::getPassRegistry());
}  
        
GroundTruth::~GroundTruth() {}


/* collect information for each function */
void GroundTruth::collectCalleeInfo(Function &F)
{
	
	errs() << "Function: ";
    errs().write_escaped(F.getName()) << " ";
    int function_parameters = F.arg_size();
    
    for(Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai != ae; ++ai)
    {
		Value *v_f = dyn_cast<Argument>(ai);
		
		Type *T = v_f->getType();
		
		
		if (T == Int32Ty)
		{
			errs() << " int ";
		}
		else if (T == Int8Ty)
		{
			errs() << " char ";
		}
		else if (T == Int64Ty)
		{
			errs() << " long ";
		}

		else if (T == Int16Ty)
		{
			errs() << " short ";
		}
		else if (T->isPointerTy() || T->isFunctionTy())
		{

			if (!dyn_cast<Argument>(ai)->hasByValAttr())
				errs() << " * ";
			else
				errs() << "struct ";
		}
		else if (T == BoolTy)
		{
			errs() << " _Bool ";
		}
		else if ( T->isFloatingPointTy() )
		{
			errs()<<" float ";
		}
		else if (T->isVectorTy())
		{
			errs() << " vector ";
		}
		else if (T->isVoidTy())
		{
			errs()<< " void ";
		}
		else if (T->isStructTy() )
			errs() << " struct ";

		else if (T->isArrayTy())
			errs() << " array ";

		
	}
	
	if (F.getFunctionType()->isVarArg())
    {
        errs() << " variadic ";
    }
    errs() <<function_parameters<<" ";

	Function::iterator B = F.begin();
	BasicBlock *BB = &*B;
	
	SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
	F.getAllMetadata(MDs);
	
	
	unsigned minimum_line = 0xffffffff;
	 StringRef File;
	 StringRef Dir;
	 
	 
	
	for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I)
	{
			Instruction *Inst = &*I;
			if (DILocation *Loc = Inst->getDebugLoc()) {  // Here I is an LLVM instruction

				unsigned Line = Loc->getLine();
				File = Loc->getFilename();
				Dir = Loc->getDirectory();

				if (Line < minimum_line)
				{
					minimum_line = Line;
				    File = File;
					Dir = Dir;
				}
			
			}

	}
	for (auto &MD : MDs) {
	  if (MDNode *N = MD.second) {
		if (auto *subProgram = dyn_cast<DISubprogram>(N)) {
		  errs() <<Dir<<"/"<< File <<":"<<subProgram->getLine();
		}
	  }
	}
	
	
	errs()<<"\n";
}




void GroundTruth::collectICallInfo(Instruction &I, CallSite &CS)
{
   
    int arg_num = CS.arg_size();
    
    CallSite::arg_iterator B = CS.arg_begin(), E = CS.arg_end();
    
    
    errs()<<"Ind-call: ";
    
    for (CallSite::arg_iterator A = B; A != E; ++A)
    {
        Value *v = dyn_cast<Value>(A);
        
        Type *Ty = v->getType();
        
    if (Ty->isIntegerTy(8))
    {
        errs()<<"char ";
    }
		else if (Ty->isIntegerTy(32))
		{
			errs()<<"int ";
		}
		else if (Ty->isIntegerTy(64))
		{
			errs()<<"long ";
		}
		else if (Ty->isIntegerTy(1))
		{
			errs()<<"_Bool ";
		}
		else if (Ty->isIntegerTy(16))
		{
			errs()<<"short ";
		}
        else if ( Ty->isFloatingPointTy() )
        {
            errs()<<"float ";
        }
        else if (Ty->isPointerTy() || Ty->isFunctionTy())
        {
            errs()<<"* ";
        }
            
        else if (Ty->isStructTy())
        {
            //result = "struct ";
            StructType *STyp = dyn_cast<StructType>(Ty);
            
            //result += STyp->getName();
            
            errs()<<"struct "+STyp->getName()+" ";
            
        }
        else if (Ty->isVectorTy())
		{
			errs() << " vector ";
		}
		else if (Ty->isVoidTy())
		{
			errs()<< " void ";
		}
		
		else if (Ty->isArrayTy())
			errs() << " array ";

    }
    errs() <<arg_num << " ";
	
	
	
	// Here I is an LLVM instruction
	if (DILocation *Loc = I.getDebugLoc()){
		unsigned Line = Loc->getLine();
		StringRef File = Loc->getFilename();
		StringRef Dir = Loc->getDirectory();

		errs()<<Dir<<"/"<< File <<":"<<Line;
	}
	errs()<<"\n";
    
}





bool GroundTruth::runOnFunction(Function &F) {
	
	collectCalleeInfo(F);
	for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
		
		CallSite CS(&I);
	
		
		if (CS && isIndirectCall(CS)){
			Value *CalledValue = CS.getCalledValue();

			// Don't rewrite this instruction if the indirect call is actually just
			// inline assembly, since our transformation will generate an invalid
			// module in that case.
			if (isa<InlineAsm>(CalledValue))
			  continue;


			collectICallInfo(I,CS);
		}
		
      }
  }

  return true;
}
