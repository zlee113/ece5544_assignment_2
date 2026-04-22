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

  /**
   * @brief Struct to hold the information for a loops dominators info
   */
  struct loop_dom
  {
    std::vector<BasicBlock *> universe;
    std::vector<BitVector> out;
  };

  loop_dom get_loop_dominators(Loop *L)
  {
    Function *F = L->getHeader()->getParent();
    /* Fills in the "universe" block with every basic block in function */
    std::vector<BasicBlock *> universe;
    std::vector<BitVector> out;
    for (BasicBlock &BB : *F)
    {
      universe.push_back(&BB);
    }

    /* Setup initial block state */
    for (int i = 0; i < universe.size(); i++)
    {
      /* Setup entry */
      if (i == 0)
      {
        BitVector entry(universe.size(), false);
        entry.set(0);
        out.push_back(entry);
      }
      /* If not entry should be top */
      else
      {
        out.push_back(BitVector(universe.size(), true));
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
          ins.push_back(out[index]);
        }
        /* Get the new out but make sure it has preds first */
        BitVector new_out;
        if (ins.empty())
        {
          new_out = out[i];
        }
        else
        {
          /* Get the new out meet of the preds for this block (intersection)*/
          new_out = meet(ins, 2);
          /* Union that new out with the current blocks value */
          new_out.set(i);
        }

        /* Check new out vs old and set the out for this basic block to the new out */
        if (new_out != out[i])
        {
          changed = true;
          out[i] = new_out;
        }
      }
    }
    loop_dom ld;
    ld.universe = universe;
    ld.out = out;
    return ld;
  }

  /**
   * @brief checks if block x dominates block y
   *
   * @param doms the loop_dom struct for this loop
   * @param x the value we want to see holds dominion over y
   * @param y the value we want to see if is dominated by x
   * @return true If it doesn't dominate
   * @return false if it doesn't dominate or isn't in the universe
   */
  bool check_if_dominates(loop_dom *doms,
                          BasicBlock *x,
                          BasicBlock *y)
  {
    /* Find the index of x in the universe*/
    auto itx = std::find(doms->universe.begin(), doms->universe.end(), x);
    if (itx == doms->universe.end())
    {
        outs() << "BasicBlock x not in universe" << "\n";
        return false;
    }

    /* Find the index of y in the universe */
    auto ity = std::find(doms->universe.begin(), doms->universe.end(), y);
    if (ity == doms->universe.end())
    {
        outs() << "BasicBlock y not in universe" << "\n";
        return false;
    }

    int index_x = std::distance(doms->universe.begin(), itx);
    int index_y = std::distance(doms->universe.begin(), ity);

   // outs() << index_x << "      " << index_y << "\n";

    /* x dominates y if the bit is set for x in the out for y */
    return doms->out[index_y].test(index_x);
  }

  // -------------------- Dominators Pass --------------------
  /**
   * @brief Functionpass for dominators
   */
  struct dominators : PassInfoMixin<dominators>
  {

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM)
    {
      outs() << "=== ";
      F.printAsOperand(outs(), false);
      outs() << " ===\n";

      /* Get the loop info for the block */
      LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
      for (Loop *L : LI)
      {
        loop_dom loop_results = get_loop_dominators(L);

        outs() << "Loop starting at: "
               << L->getHeader()->getName() << "\n";

        /* Print outs cleanly */
        for (int i = 0; i < loop_results.universe.size(); i++)
        {
          outs() << "BB: ";
          loop_results.universe[i]->printAsOperand(outs(), false);
          outs() << "\n";
          printBasicBlockBitSet(outs(), "OUT", loop_results.out[i], loop_results.universe);
        }

        /* Print out the closest dominator */
        for (int i = 1; i < loop_results.universe.size(); i++)
        {
          int index = -1;
          for (int j = 0; j < loop_results.universe.size(); j++)
          {
            if (j != i && loop_results.out[i].test(j))
            {
              index = j;
            }
          }

          if (index != -1)
          {
            outs() << loop_results.universe[i]->getName()
                   << " is dominated by "
                   << loop_results.universe[index]->getName()
                   << "\n";
          }
        }
      }
      return PreservedAnalyses::all();
    }
  };

  struct dead_code_elimination : PassInfoMixin<dead_code_elimination>
  {
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
          /* Add instructions to the universe if they have a value */
          if (!I.getType()->isVoidTy() &&
              !I.getType()->isPointerTy() &&
              !isLive(&I))
          {
            universe.push_back(&I);
          }
        }
      }
      /* Removes any duplicates from the list */
      std::sort(universe.begin(), universe.end());
      universe.erase(std::unique(universe.begin(), universe.end()), universe.end());
      // Create a vector for backwards traversal through the tree
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

      /* Creates bitvector with every bit set the size of the universe */
      BitVector all(universe.size(), true);
      std::vector<BasicBlock *> worklist;
      DenseMap<BasicBlock *, BitVector> in;
      DenseMap<Instruction *, BitVector> out;
      for (BasicBlock *BB : order)
      {
        /* Default in: full set */
        in[BB] = BitVector(universe.size(), true);
        /* Default out: full set */
        for (Instruction &I : *BB)
        {
          out[&I] = BitVector(universe.size(), true);
        }

        /* Add the exit block to the list the rest will be added at the loop */
        if (succ_begin(BB) == succ_end(BB))
          worklist.push_back(BB);
      }

      /* Worklist loop, ending only when empty */
      while (!worklist.empty())
      {
        /* Get last block in the worklist */
        BasicBlock *B = worklist.back();
        worklist.pop_back();

        /* Meet operation for intersection */
        std::vector<BitVector> succIns;
        for (BasicBlock *succ : successors(B))
          succIns.push_back(in[succ]);
        // if our list of successors is empty, add an empty bitvector
        if (succIns.empty())
          succIns.push_back(BitVector(universe.size(), true));
        BitVector x = meet(succIns, 2);

        /* Instruction level transfer function */
        for (auto it = B->rbegin(); it != B->rend(); ++it)
        {
          Instruction &I = *it;
          out[&I] = x;

          /* Calc gen set */
          BitVector gen(universe.size(), false);
          if (!I.getType()->isVoidTy() && !I.getType()->isPointerTy())
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
                gen.set(index);
              }
            }
          }

          /* Calc kill set */
          BitVector const_kill = BitVector(universe.size(), false);
          /* Get all the RHS operands */
          if (I.getType()->isVoidTy() || I.isTerminator())
          {
            for (Use &U : I.operands())
            {
              /* Make sure they aren't constant values */
              if (!isa<ConstantInt>(U.get()))
              {
                /* Find where it is in the universe */
                auto it = std::find(universe.begin(), universe.end(), U.get());
                if (it != universe.end())
                {
                  /* Get the distance from the start for index */
                  int index = std::distance(universe.begin(), it);
                  /* Set the bit */
                  const_kill.set(index);
                }
              }
            }
          }
          BitVector dep_kill = BitVector(universe.size(), false);
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
              if (!x.test(index))
              {
                /* Get all the RHS operands */
                for (Use &U : I.operands())
                {
                  /* Make sure they aren't constant values */
                  if (!isa<ConstantInt>(U.get()))
                  {
                    /* Find where it is in the universe */
                    it = std::find(universe.begin(), universe.end(), U.get());
                    if (it != universe.end())
                    {
                      /* Get the distance from the start for index */
                      int index = std::distance(universe.begin(), it);
                      /* Set the bit */
                      dep_kill.set(index);
                    }
                  }
                }
              }
            }
          }
          /* Union the two kills */
          BitVector kill = const_kill;
          kill |= dep_kill;

          /* Get the next x value */
          /* FaintIn = (FaintOut - FaintKill) U FaintGen */
          BitVector new_x = x;
          new_x.reset(kill);
          new_x |= gen;
          x = new_x;
        }

        /* Check the values for in */
        BitVector new_in = x;
        if (new_in != in[B])
        {
          in[B] = new_in;
          for (BasicBlock *pred : predecessors(B))
          {
            if (std::find(worklist.begin(), worklist.end(), pred) == worklist.end())
            {
              worklist.push_back(pred);
            }
          }
        }
      }

      /* Get the instructions we want to delete */
      std::vector<Instruction *> instr_to_delete;
      for (BasicBlock *BB : order)
      {
        for (Instruction &I : *BB)
        {
          /* Make sure the instruction isn't live or one we don't want to delete */
          if (!isLive(&I) && !I.getType()->isVoidTy() && !I.getType()->isPointerTy())
          {
            auto it = std::find(universe.begin(), universe.end(), &I);
            if (it != universe.end())
            {
              /* Grab the index and test it */
              int index = std::distance(universe.begin(), it);
              if (out[&I].test(index))
              {
                outs() << "Removing Instruction ";
                I.print(outs());
                outs() << "\n";
                instr_to_delete.push_back(&I);
              }
            }
          }
        }
      }

      /* Loop through the vector we made and delete all the instructions */
      for (Instruction *I : instr_to_delete)
      {
        I->eraseFromParent();
      }
      return PreservedAnalyses::all();
    }
  };

  struct loop_invariant_code_motion : PassInfoMixin<loop_invariant_code_motion>
  {
    bool isInvariant(Instruction *I, Loop *L)
    {
      std::vector<BasicBlock *> BB = L->getBlocksVector();
      bool validInstType = false, defReaching = false;
      validInstType = (isa <BinaryOperator>(I) || I->isShift() || isa <SelectInst>(I) || isa <CastInst>(I) || isa <GetElementPtrInst>(I));
      //outs() << I->getOpcodeName() << "      " << validInstType << "\n";
      return (validInstType && ReachingPass(I, L));
    }

    bool safeToHoist(Instruction* I, Loop* L)
    {
        loop_dom doms = get_loop_dominators(L);
        //SmallVector<BasicBlock*, 8> ExitBlocks;
        //L->getExitBlocks(ExitBlocks);

        std::vector <BasicBlock*> exitBB;
        std::vector<BasicBlock*> BB = L->getBlocksVector();

        for (auto& B : BB)
        {
            if (L->isLoopExiting(B))
                for (BasicBlock* succ : successors(B))
                {
                    if (!L->contains(succ))
                        exitBB.push_back(succ);
                }
        }

        for (auto& B : exitBB)
        {
           // outs() << isSafeToSpeculativelyExecute(I) << "     " << check_if_dominates(&doms, I->getParent(), B) << "\n";
            if (!(isSafeToSpeculativelyExecute(I) || check_if_dominates(&doms, I->getParent(), B)))
                return false;
        }
        return true;
    }

    bool ReachingPass(Instruction *inst, Loop *L)
    {
      /*bool reaches = true;
      std::vector<BasicBlock *> BB = L->getBlocksVector();
      for (auto &B : BB)
      {
        for (auto &it : *B)
        {
          if (&it == I)
            return reaches;
          else
          {
              if (I->getNumOperands() == 2)
              {
                Value *V = cast<Value>(I);
                if (V == it.getOperand(0))
                  reaches = false;
              }
              else if (I->getNumOperands() == 3)
              {
                Value *V = cast<Value>(I);
                if (V == it.getOperand(0) || V == it.getOperand(1))
                  reaches = false;
              }
            }
        }*/

        Function* F = L->getHeader()->getParent();

        struct BlockState
        {
            BitVector in;
            BitVector out;
            BitVector gen;
            BitVector kill;
        };

        std::vector<Instruction*> universe;
        for (auto& BB : *F)
        {
            for (auto& I : BB)
            {
                if (!I.getType()->isVoidTy())
                {
                    universe.push_back(&I);
                }
            }
        }

        /* Creating a vector for the order of traversal through the tree */
        DenseMap<const BasicBlock*, BlockState> st;
        std::vector<BasicBlock*> order;
        order.push_back(&F->getEntryBlock());
        for (size_t i = 0; i < order.size(); ++i)
        {
            for (BasicBlock* succ : successors(order[i]))
            {
                if (std::find(order.begin(), order.end(), succ) == order.end())
                    order.push_back(succ);
            }
        }

        /* Creates bitvector with every bit set the size of the universe */
        BitVector all(universe.size(), true);
        for (BasicBlock* BB : order)
        {
            BlockState bs;
            /* Default in: empty set */
            bs.in = BitVector(universe.size(), false);
            /* Default out: Var if not entry */
            bs.out = BitVector(universe.size(), false);
            /* Default gen: empty set */
            bs.gen = BitVector(universe.size(), false);
            /* Default kill: empty set */
            bs.kill = BitVector(universe.size(), false);

            for (Instruction& I : *BB)
            {
                if (!I.getType()->isVoidTy())
                {
                    /* Gets value of said instruction in the universe */
                    auto it = std::find(universe.begin(), universe.end(), &I);
                    /* Add to gen if expression matches and isn't end */
                    if (it != universe.end())
                        bs.gen.set(static_cast<unsigned>(it - universe.begin()));
                    for (size_t i = 0; i < universe.size(); ++i)
                    {
                        /* If the instruction defines a value a expression in universe uses it add it to kill */
                        if (universe[i] == &I)
                            bs.kill.set(static_cast<unsigned>(i));
                    }
                }
            }

            /* Make kill not invalidate newly gen expressions and add it */
            BitVector notGen = bs.gen;
            bs.kill &= notGen.flip();
            st[BB] = bs;
        }

        /* Iterative section for finding in and out */
        bool changed = true;
        while (changed)
        {
            /* Fixed point check */
            changed = false;
            for (BasicBlock* BB : order)
            {
                /* Get pred outs */
                std::vector<BitVector> predOuts;
                /* If starting outs is empty */
                if (BB == &F->getEntryBlock())
                    predOuts.push_back(BitVector(universe.size(), false));
                /* Checks all predecessors and add up their outs */
                for (BasicBlock* pred : predecessors(BB))
                    predOuts.push_back(st[pred].out);
                /* If predecessors outs was empty push empty bitvector */
                if (predOuts.empty())
                    predOuts.push_back(BitVector(universe.size(), false));

                /* Set in to intersection of all previous outs */
                st[BB].in = meet(predOuts, 1);

                /* Compute new out as GEN U (IN - KILL)*/
                BitVector newOut = st[BB].in;
                newOut.reset(st[BB].kill);
                newOut |= st[BB].gen;

                if (newOut != st[BB].out)
                {
                    st[BB].out = newOut;
                    changed = true;
                }
            }
        }


        //an instruction reaches if its definition is in the out vector of the loop header
        auto it = std::find(universe.begin(), universe.end(), inst);
        int index = std::distance(universe.begin(), it);
        //auto ity = std::find(st[L->getHeader()].out.begin(), st[L->getHeader()].out.end(), static_cast<unsigned>(it - universe.begin()));
        if (it != universe.end())
            outs() << st[L->getHeader()].out.test(static_cast<unsigned>(it - universe.begin())) << "\n";
            //outs() << "test\n";
        //return (ity == universe.end());

        //return doms->out[index].test(static_cast<unsigned>(it - universe.begin()));
        return st[L->getHeader()].out.test(static_cast<unsigned>(it - universe.begin()));
      }

    PreservedAnalyses run(Loop& L, LoopAnalysisManager& AM, LoopStandardAnalysisResults& res, LPMUpdater& updater)
    {
      outs() << "PASS RUNNING ON: " << L.getName() << "\n";

       llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop> *KLoop = new llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>();
      llvm::DominatorTree *DT = new llvm::DominatorTree(*L.getHeader()->getParent());
      KLoop->analyze(*DT);
      //KLoop->print(outs());
      //outs() << "\n";

      std::vector<Instruction*> instsToMove;

        if (L.getLoopPreheader() != NULL)
        {
            //Find all blocks dominated by loop header
          std::vector <BasicBlock*> domBB;
          std::vector<BasicBlock *> BB = L.getBlocksVector();
          loop_dom doms = get_loop_dominators(&L);

          for (auto& B : BB)
          {
              if (check_if_dominates(&doms, L.getHeader(), B))
                  domBB.push_back(B);
          }

          for (auto &B : domBB)
          {
              //outs() << KLoop->getLoopFor(B)->getLoopDepth() << "     " << &L << "\n";
              if (KLoop->getLoopFor(B) != NULL && KLoop->getLoopFor(B)->getLoopDepth() == 1)
              {
                  for (auto& I : *B)
                  {
                      if (!(I.getType()->isVoidTy()))
                      {
                          // Run a dominators and reaching definitions pass to see if an instruction can be safely moved outside the loop
                          if (isInvariant(&I, &L) && safeToHoist(&I, &L))
                          {
                              //outs() << "progress \n";
                              //If the instruction can be moved, add it to the vector of instructions to move
                              instsToMove.push_back(&I);
                          }
                      }
                  }
              }
          }

          for (auto& I : instsToMove)
          {
              outs() << I->getOpcodeName() << "\n";
              I->moveAfter(L.getLoopPreheader()->begin());
              //I->updateLocationAfterHoist();
              //I->removeFromParent();
          }
        }
      
      return PreservedAnalyses::all();
    }
  };
} // namespace
extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo()
{
  return {
      LLVM_PLUGIN_API_VERSION, "UnifiedPass", "v0.3-starter", [](PassBuilder &PB)
      {
        PB.registerPipelineParsingCallback(
            [](StringRef Name, FunctionPassManager& FPM,
               ArrayRef<PassBuilder::PipelineElement>) -> bool
            {
              if (Name == "dominators")
              {
                FPM.addPass(dominators());
                return true;
              }
              if (Name == "dead-code-elimination")
              {
                FPM.addPass(dead_code_elimination());
                return true;
              }
              return false;
            });
        PB.registerPipelineParsingCallback(
            [](StringRef Name, LoopPassManager& LPM,
               ArrayRef<PassBuilder::PipelineElement>) -> bool
            {
              if (Name == "loop-invariant-code-motion")
              {
                LPM.addPass(loop_invariant_code_motion());
                return true;
              }
              return false;
            });
      }};
}
