// ECE/CS 5544 Assignment 2 starter unifiedpass.cpp
// Lean starter: buildable scaffolds, minimal solved logic.

#include <algorithm>
#include <cstdint>
#include <numeric>
#include <string>
#include <vector>
#include <stack>

#include <llvm/ADT/BitVector.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/GenericLoopInfo.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/ValueTracking.h>

using namespace llvm;

namespace
{
  // the same as printBitSet, but for when you know the universe vector is of Value* type
  void printValueBitSet(raw_ostream &OS, StringRef label, const BitVector &bits, const std::vector<BasicBlock *> universe)
  {
    OS << "  " << label << ": { ";
    bool first = true;
    for (unsigned i = 0; i < bits.size(); ++i)
    {
      if (!bits.test(i))
        continue;
      if (!first)
        OS << "; ";
      first = false;
      universe[i]->printAsOperand(OS, false);
    }
    OS << " }\n";
  }
  // -------------------- Dominators Pass --------------------
  /**
   * @brief Functionpass for dominators
   */
  struct dominators : PassInfoMixin<dominators>
  {
    /**
     * @brief Each set we need to generate for the pass
     */
    struct BlockState
    {
      std::vector<BitVector> in;
      std::vector<BitVector> out;
    };

    /**
     * @brief The meet function for a union of all the succs for function
     *
     * @param ins Bitvectors for all succs of this node
     * @param type Type of meet, 1 for union, 2 for intersection
     * @return BitVector
     */
    static BitVector meet(const std::vector<BitVector> &ins, uint8_t type)
    {
      // If its empty the bitwise or will yield nothing
      if (ins.empty())
        return {};
      /* Start with first element and then for each bit with each bit in all other ins*/
      BitVector out = ins[0];
      for (size_t i = 1; i < ins.size(); ++i)
      {
        /* Union */
        if (type == 1)
        {
          out |= ins[i];
        }
        else if (type == 2)
        {
          out &= ins[i];
        }
      }

      return out;
    }

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
    {
      outs() << "PASS RUNNING ON: " << F.getName() << "\n";
      /* Fills in the "universe" block with every basic block in function */
      std::vector<BasicBlock *> universe;
      for (auto &BB : F)
      {
        universe.push_back(&BB);
      }

      /* Setup initial block state */
      BlockState bs;
      for (int i = 0; i < universe.size(); i++)
      {
        /* Setup entry */
        if (i == 0)
        {
          BitVector entry(universe.size(), false);
          entry.set(0);
          bs.out.push_back(entry);
        }
        /* If not entry should be top */
        else
        {
          bs.out.push_back(BitVector(universe.size(), true));
        }
      }

      /* Find Dominators */
      bool changed = true;
      while (changed)
      {
        changed = false;
        for (int i = 0; i < universe.size(); i++)
        {
          /* Get all the ins for this block to put through the meet function */
          std::vector<BitVector> ins;
          for (auto *pred : predecessors(universe[i]))
          {
            /* We need to find the element of the pred to add it to ins properly */
            auto it = std::find(universe.begin(), universe.end(), pred);
            int index = std::distance(universe.begin(), it);
            /* Add it to ins */
            ins.push_back(bs.out[index]);
          }
          /* Get the new out but make sure it has preds first */
          BitVector new_out;
          if (ins.empty())
          {
            new_out = bs.out[i];
          }
          else
          {
            /* Get the new out meet of the preds for this block (intersection)*/
            new_out = meet(ins, 2);
            /* Union that new out with the current blocks value */
            new_out.set(i);
          }

          /* Check new out vs old and set the out for this basic block to the new out */
          if (new_out != bs.out[i])
          {
            changed = true;
            bs.out[i] = new_out;
          }
        }
      }
      /* Nice print for each basic block all the required fields */
      for (int i = 0; i < universe.size(); i++)
      {
        outs() << "BB: ";
        universe[i]->printAsOperand(outs(), false);
        outs() << "\n";
        printValueBitSet(outs(), "OUT", bs.out[i], universe);
      }
      /* Print out the closest dominator */
      for (int i = 1; i < universe.size(); i++)
      {
        int index = -1;
        for (int j = 0; j < universe.size(); j++)
        {
          if (j != i && bs.out[i].test(j))
          {
            index = j;
          }
        }

        if (index != -1)
        {
          outs() << universe[i]->getName()
                 << " is dominated by "
                 << universe[index]->getName()
                 << "\n";
        }
      }
      return PreservedAnalyses::all();
    }
  };

  struct loop_invariant_code_motion : PassInfoMixin<loop_invariant_code_motion>
  {
      bool isInvariant(Instruction* I, Loop* L, DominatorTree* DT)
      {
          bool invariant = true;
          std::vector<BasicBlock*> BB = L->getBlocksVector();
          for (auto& B : BB)
          {
              if (isSafeToSpeculativelyExecute(I) && !I->mayReadFromMemory()
                  && !isa<LandingPadInst>(I) && ReachingPass(I, L) && DT->dominates(I, B))
                  return false;
          }
          return true;
      }
          
      bool ReachingPass (Instruction* I, Loop* L)
      {
          bool reaches = true;
          std::vector<BasicBlock*> BB = L->getBlocksVector();
          for (auto& B : BB)
          {
              for (auto& it : *B)
              {
                  if (&it == I)
                      return reaches;
                  else
                  {
                      if (!I->getType()->isVoidTy())
                      {
                          if (I->getNumOperands() == 2)
                          {
                              Value* V = cast<Value>(I);
                              if (V == it.getOperand(0))
                                  reaches = false;
                          }
                          else if (I->getNumOperands() == 3)
                          {
                              Value* V = cast<Value>(I);
                              if (V == it.getOperand(0) || V == it.getOperand(1))
                                  reaches = false;
                          }
                      }
                  }
              }
          }
          return reaches;
      }

      PreservedAnalyses run(Function& F, FunctionAnalysisManager&)
      {
          outs() << "PASS RUNNING ON: " << F.getName() << "\n";

          //Step 1: Find the loops. Create a bool for if a nested loop is found, telling the code to recheck loop bodies for potential further bubbling
          llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>* KLoop = new llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>();
          llvm::DominatorTree* DT = new llvm::DominatorTree(F);
          KLoop->analyze(*DT);
          KLoop->print(outs());
          outs() << "\n";

          for (std::vector<Loop*>::const_iterator it = KLoop->begin(); it != KLoop->end(); ++it)
          {
              if (((Loop*)*it)->getLoopPreheader() != NULL)
              {
                  /*Step 2: Place two empty basic blocks BETWEEN the loop preheader and the loop header
                  the upper block should be an unconditional landing block where all INVARIANT instructions go
                  the lower block should be a conditional block that replicates the branch condition of the original loop header
                  make sure to edit the CFG and provide a path from the conditional block to the loop exit
                  make sure the loop is executed AT LEAST once*/
                  BasicBlock* uncondBlock = BasicBlock::Create(F.getContext(), "uncondLandingPlatform", &F);
                  IRBuilder<> uncondBuilder(uncondBlock);
                  uncondBuilder.SetInsertPoint(uncondBlock);
                  BranchInst* uncondEnd = uncondBuilder.CreateBr(uncondBlock);
                  BasicBlock* condBlock = BasicBlock::Create(F.getContext(), "condLandingPlatform", &F);
                  IRBuilder<> condBuilder(condBlock);
                  condBuilder.SetInsertPoint(condBlock);
                  BranchInst* condEnd = condBuilder.CreateBr(condBlock);

                  std::vector<BasicBlock*> BB = ((Loop*)*it)->getBlocksVector();
                  for (auto& B : BB)
                  {
                      for (auto& I : *B)
                      {
                          //Step 3: Run a dominators and reaching definitions pass to see if an instruction can be safely moved outside the loop
                          if (isInvariant(&I, ((Loop*)*it), new llvm::DominatorTree(F)))
                          {
                              outs() << "progress \n";
                              //Step 4: If the instruction can be moved, move it to the new unconditional block. Otherwise, move it to the new conditional block
                              //Instruction* newInst = I.clone();
                              //newInst->insertBefore(uncondBlock->end()->getPrevNode());
                              //I.removeFromParent();
                          }
                          else
                          {
                              //Instruction* newInst = I.clone();
                              //newInst->insertBefore(condBlock->end()->getPrevNode());
                              //I.removeFromParent();
                          }
                      }

                  }
              }
          }




          return PreservedAnalyses::all();
      }
  };
} // namespace
extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo()
{
  return {LLVM_PLUGIN_API_VERSION, "UnifiedPass", "v0.3-starter", [](PassBuilder &PB)
          {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) -> bool
                {
                  if (Name == "dominators")
                  {
                    FPM.addPass(dominators());
                    return true;
                  }
                  else if (Name == "loop_invariant_code_motion")
                  {
                      FPM.addPass(loop_invariant_code_motion());
                      return true;
                  }
                  return false;
                });
          }};
}
