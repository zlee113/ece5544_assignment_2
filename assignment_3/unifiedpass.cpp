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
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;

namespace
{
  // the same as printBitSet, but for when you know the universe vector is of Value* type
  void printBasicBlockBitSet(raw_ostream &OS, StringRef label, const BitVector &bits, const std::vector<BasicBlock *> universe)
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
  void printValueBitSet(raw_ostream &OS, StringRef label, const BitVector &bits, const std::vector<Value *> universe)
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

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
    {
      outs() << "=== ";
      F.printAsOperand(outs(), false);
      outs() << " ===\n";
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
        printBasicBlockBitSet(outs(), "OUT", bs.out[i], universe);
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

  struct dead_code_elimination : PassInfoMixin<dead_code_elimination>
  {
    /**
     * @brief Each set we need to generate for the pass
     */
    struct BlockState
    {
      BitVector in;
      BitVector out;
      BitVector gen;
      BitVector kill;
      BitVector use;
    };
    /**
     * @brief IsLive instruction
     *
     * @param I
     * @return true
     * @return false
     */
    bool isLive(Instruction *I)
    {
      return I->isTerminator() ||
             isa<DbgInfoIntrinsic>(I) ||
             isa<LandingPadInst>(I) ||
             I->mayHaveSideEffects();
    }
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
    {
      outs() << "=== ";
      F.printAsOperand(outs(), false);
      outs() << " ===\n";
      /* Fills in the "universe" block with every operand in function */
      std::vector<Value *> universe;
      for (auto &BB : F)
      {
        for (auto &I : BB)
        {
          if (!I.getType()->isVoidTy())
          {
            // if the values aren't constants add them to the vector
            for (Use &U : I.operands())
            {
              if (!isa<Constant>(U.get()) && !(U.get()->getType()->isPointerTy()) && !U.get()->getType()->isVoidTy())
                universe.push_back(U.get());
            }
          }
          if (!(I.getType()->isPointerTy()) && !(I.getType()->isVoidTy()))
          {
            universe.push_back(&I);
          }
        }
      }
      /* Removes any duplicates from the list */
      std::sort(universe.begin(), universe.end());
      universe.erase(std::unique(universe.begin(), universe.end()), universe.end());
      for (int i = 0; i < universe.size(); i++)
      {
        outs() << i << ": ";
        universe[i]->printAsOperand(outs(), false);
        outs() << " type: ";
        universe[i]->getType()->print(outs());
        outs() << "\n";
      }
      // Create a vector for backwards traversal through the tree
      DenseMap<const BasicBlock *, BlockState> st;
      std::vector<BasicBlock *> order;
      order.push_back(&F.getEntryBlock());
      for (size_t i = 0; i < order.size(); ++i)
      {
        for (BasicBlock *succ : successors(order[i]))
        {
          if (std::find(order.begin(), order.end(), succ) == order.end())
            order.push_back(succ);
        }
      }
      /* Now flip the order so its reversed*/
      std::reverse(order.begin(), order.end());

      /* Creates bitvector with every bit set the size of the universe */
      BitVector all(universe.size(), true);
      for (BasicBlock *BB : order)
      {
        BlockState bs;
        /* Default in: full set */
        bs.in = BitVector(universe.size(), false);
        /* Default out: full set */
        bs.out = BitVector(universe.size(), true);
        /* Default gen: empty set */
        bs.gen = BitVector(universe.size(), false);
        /* Default kill: empty set */
        bs.kill = BitVector(universe.size(), false);
        /* Default use: empty set */
        bs.use = BitVector(universe.size(), false);

        /* Creating the gen and use sets since their static */
        for (Instruction &I : *BB)
        {
          /* Make sure instruction isn't void type */
          if (!I.getType()->isVoidTy())
          {
            /* Grab the left hand side (just the instruction)*/
            Value *LHS = &I;
            /* Iterate through the right hand side and compare to lhs */
            bool lhs_in_rhs = false;
            for (Use &U : I.operands())
            {
              if (LHS == U.get())
              {
                lhs_in_rhs = true;
              }
            }
            /* If the LHS isn't in the RHS we can add it to the gen set */
            if (!lhs_in_rhs)
            {
              /* Find where it is in the universe */
              auto it = std::find(universe.begin(), universe.end(), LHS);
              /* Get the distance from the start for index */
              if (it != universe.end())
              {
                int index = std::distance(universe.begin(), it);
                /* Set the bit */
                bs.gen.set(index);
              }
            }
          }
          else
          {
            /* Get all the RHS operands */
            for (Use &U : I.operands())
            {
              /* Make sure they aren't constant values */
              if (!isa<ConstantInt>(U.get()))
              {
                /* Find where it is in the universe */
                auto it = std::find(universe.begin(), universe.end(), U.get());
                /* Get the distance from the start for index */
                if (it != universe.end())
                {
                  int index = std::distance(universe.begin(), it);
                  /* Set the bit */
                  bs.use.set(index);
                }
              }
            }
          }
        }
        /* Update the block state for each basic block */
        st[BB] = bs;
      }
      /* Iterative section for finding in, out, and kill */
      bool changed = true;
      while (changed)
      {
        /* Fixed point check */
        changed = false;
        for (BasicBlock *BB : order)
        {
          /* Reset the kill for this block (updated cleanly each iteration) */
          st[BB].kill.reset();
          /* Loop through instructions */
          for (Instruction &I : *BB)
          {
            /* Make sure instruction isn't void type */
            if (!I.getType()->isVoidTy())
            {
              /* Grab the left hand side (just the instruction)*/
              Value *LHS = &I;
              /* Find where it is in the universe */
              auto it = std::find(universe.begin(), universe.end(), LHS);
              /* Get the distance from the start for index */
              if (it != universe.end())
              {
                int index = std::distance(universe.begin(), it);
                /* Check if the bit is set in the out for this block */
                if (!st[BB].out.test(index))
                {
                  /* Get all the RHS operands */
                  for (Use &U : I.operands())
                  {
                    /* Make sure they aren't constant values */
                    if (!isa<ConstantInt>(U.get()))
                    {
                      /* Find where it is in the universe */
                      if (it != universe.end())
                      {
                        auto it = std::find(universe.begin(), universe.end(), U.get());

                        /* Get the distance from the start for index */
                        int index = std::distance(universe.begin(), it);
                        /* Set the bit */
                        st[BB].kill.set(index);
                      }
                    }
                  }
                }
              }
            }
          }
          /* Finish kill set by union with use set */
          st[BB].kill |= st[BB].use;

          /* FaintIn = (FaintOut - FaintKill) U FaintGen */
          BitVector new_in = st[BB].out;
          new_in.reset(st[BB].kill);
          new_in |= st[BB].gen;
          /* FaintOut is the intersection of all the successors */
          std::vector<BitVector> succIns;
          for (BasicBlock *succ : successors(BB))
            succIns.push_back(st[succ].in);
          // if our list of successors is empty, add an empty bitvector
          if (succIns.empty())
            succIns.push_back(BitVector(universe.size(), true));

          // set our out set to the intersection of all successors
          BitVector new_out = meet(succIns, 2);
          /* Change if the in or out are different */
          if (BB->getName().contains("12") || BB->getName().empty())
          {
            outs() << "BLOCK: ";
            BB->printAsOperand(outs(), false);
            outs() << "\n";
            printValueBitSet(outs(), "out", st[BB].out, universe);
            printValueBitSet(outs(), "kill", st[BB].kill, universe);
            printValueBitSet(outs(), "gen", st[BB].gen, universe);
            printValueBitSet(outs(), "new_in", new_in, universe);
            printValueBitSet(outs(), "new_out", new_out, universe);
            outs() << "changed: " << changed << "\n";
          }
          if (new_in != st[BB].in || new_out != st[BB].out)
          {
            /* If either is replace both and report changed as true again */
            st[BB].in = new_in;
            st[BB].out = new_out;
            changed = true;
          }
        }
      }

      /* Nice print for each basic block all the required fields */
      for (BasicBlock *BB : order)
      {
        outs() << "BB: ";
        BB->printAsOperand(outs(), false);
        outs() << "\n";
        printValueBitSet(outs(), "use", st[BB].use, universe);
        printValueBitSet(outs(), "gen", st[BB].gen, universe);
        printValueBitSet(outs(), "kill", st[BB].kill, universe);
        printValueBitSet(outs(), "IN", st[BB].in, universe);
        printValueBitSet(outs(), "OUT", st[BB].out, universe);
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
                  else if (Name == "dead-code-elimination")
                  {
                    FPM.addPass(dead_code_elimination());
                    return true;
                  }
                  return false;
                });
          }};
}
