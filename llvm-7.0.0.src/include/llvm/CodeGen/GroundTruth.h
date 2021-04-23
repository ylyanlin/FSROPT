

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Pass.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Type.h"

#include <string>


namespace llvm {
class AnalysisUsage;
class BasicBlock;
class Constant;
class Function;
class Instruction;
class Module;
class Value;

class GroundTruth : public FunctionPass {
public:
	static char ID;
	GroundTruth();
	~GroundTruth() override;
	
	bool runOnFunction(Function &F) override;
	
	bool doInitialization(Module &M) override;
	
	
	StringRef getPassName() const override {
		return "Get ground truth for indirect call";
	}
	
	//void getAnalysisUsage(AnalysisUsage &AU) const override;
	
private:
	void collectCalleeInfo(Function &F);
	void collectCallerInfo(Instruction &I, CallSite &CS);
    void collectICallInfo (Instruction &I, CallSite &CS);
	void collectReturnType(Function &F);
	/*typedef SmallVector<Instruction *, 64> CallSet;
	CallSet IndirectCalls;
	void getIndirectCalls(Module &M);
	void collectInfo();*/
	const DataLayout *DL;
	//Type *CharPtrTy;
	//Type *VoidPtrTy;
    Type *IntPtrTy;
    Type *Int32Ty;
    Type *Int8Ty;
    Type *Int64Ty;
    Type *Int128Ty;
    Type *Int16Ty;
    Type *BoolTy;
    Type *StructTy;
	Type *EnumTy;
};
FunctionPass *createGroundTruthPass();

}
