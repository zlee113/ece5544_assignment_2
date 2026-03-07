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

    /**
     * @brief Get the Short Value Name object
     *
     * @param V Value we want to obtain a string form of
     * @return std::string
     */
    std::string getShortValueName(const Value* V)
    {
      return {BO.getOpcode(), BO.getOperand(0), BO.getOperand(1)};
    }
  };

  /**
   * @brief Overload for expression printing
   *
   * @param OS Stream being printed to
   * @param E Expression being printed
   * @return raw_ostream&
   */
  raw_ostream &operator<<(raw_ostream &OS, const Expr &E)
  {
    OS << getShortValueName(E.lhs) << " ";
    switch (E.opcode)
    {
    case Instruction::Add:
      OS << "+";
      break;
    case Instruction::Sub:
      OS << "-";
      break;
    case Instruction::Mul:
      OS << "*";
      break;
    case Instruction::SDiv:
    case Instruction::UDiv:
      OS << "/";
      break;
    default:
      OS << "(op)";
      break;
    }
    OS << " " << getShortValueName(E.rhs);
    return OS;
  }

  /**
   * @brief Print bitvector as set of expressiosn
   *
   * @param OS Stream being printed to
   * @param label Name for bitvector
   * @param bits bits in use
   * @param universe Actual bitvector
   */
  void printBitSet(raw_ostream &OS, StringRef label, const BitVector &bits, const std::vector<Expr> &universe)
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
      OS << universe[i];
    }
    OS << " }\n";
  }

  /**
   * @brief Print bitvector as set of instructions
   *
   * @param OS Stream being printed to
   * @param label Name for bitvector
   * @param bits bits in use
   * @param universe Actual bitvector
   */
  void printBitSet(raw_ostream &OS, StringRef label, const BitVector &bits, const std::vector<Instruction *> &universe)
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

  //the same as printBitSet, but for when you know the universe vector is of Value* type
  void printValueBitSet(raw_ostream& OS, StringRef label, const BitVector& bits, const std::vector<Value*> universe)
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
   * @brief Functionpass for available expression
   */
  struct AvailablePass : PassInfoMixin<AvailablePass>
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
    };

    /**
     * @brief The meet function for an intersection of all the preds for function
     *
     * @param ins Bitvectors for all preds of this node
     * @return BitVector
     */
    static BitVector meetIntersect(const std::vector<BitVector> &ins)
    {
      /* If its empty nothing will intersect */
      if (ins.empty())
        return {};
      /* Start with first element and then and each bit with each bit in all other ins*/
      BitVector out = ins[0];
      for (size_t i = 1; i < ins.size(); ++i)
        out &= ins[i];
      return out;
    }

    /* Actual pass for available expression */
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
    {
      outs() << "=== ";
      F.printAsOperand(outs(), false);
      outs() << " ===\n";

      /* Fills in the "universe" block with every instruction in function */
      std::vector<Expr> universe;
      for (auto &BB : F)
      {
        for (auto &I : BB)
        {
          if (auto *BO = dyn_cast<BinaryOperator>(&I))
            universe.push_back(Expr::fromBO(*BO));
        }
      }
      /* Removes any duplicates from the list */
      std::sort(universe.begin(), universe.end());
      universe.erase(std::unique(universe.begin(), universe.end()), universe.end());

      /* Creating a vector for the order of traversal through the tree */
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

      /* Creates bitvector with every bit set the size of the universe */
      BitVector all(universe.size(), true);
      for (BasicBlock *BB : order)
      {
        BlockState bs;
        /* Default in: empty set */
        bs.in = BitVector(universe.size(), false);
        /* Default out: Var */
        bs.out = all;
        /* Default gen: empty set */
        bs.gen = BitVector(universe.size(), false);
        /* Default kill: empty set */
        bs.kill = BitVector(universe.size(), false);

        for (Instruction &I : *BB)
        {
          if (auto *BO = dyn_cast<BinaryOperator>(&I))
          {
            /* Gets expression from each instruction in basic block */
            Expr e = Expr::fromBO(*BO);
            /* Gets value of said instruction in the universe */
            auto it = std::lower_bound(universe.begin(), universe.end(), e);
            /* Add to gen if expression matches and isn't end */
            if (it != universe.end() && *it == e)
              bs.gen.set(static_cast<unsigned>(it - universe.begin()));
          }
          if (!I.getType()->isVoidTy())
          {
            for (size_t i = 0; i < universe.size(); ++i)
            {
              /* If the instruction defines a value a expression in universe uses it add it to kill */
              if (universe[i].lhs == &I || universe[i].rhs == &I)
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
        for (BasicBlock *BB : order)
        {
          /* Get pred outs */
          std::vector<BitVector> predOuts;
          /* If starting outs is empty */
          if (BB == &F.getEntryBlock())
            predOuts.push_back(BitVector(universe.size(), false));
          /* Checks all predecessors and add up their outs */
          for (BasicBlock *pred : predecessors(BB))
            predOuts.push_back(st[pred].out);
          /* If predecessors outs was empty push empty bitvector */
          if (predOuts.empty())
            predOuts.push_back(BitVector(universe.size(), false));

          /* Set in to intersection of all previous outs */
          st[BB].in = meetIntersect(predOuts);

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

      /* Nice print for each basic block all the required fields */
      for (BasicBlock *BB : order)
      {
        outs() << "BB: ";
        BB->printAsOperand(outs(), false);
        outs() << "\n";
        printBitSet(outs(), "gen", st[BB].gen, universe);
        printBitSet(outs(), "kill", st[BB].kill, universe);
        printBitSet(outs(), "IN", st[BB].in, universe);
        printBitSet(outs(), "OUT", st[BB].out, universe);
      }
      return PreservedAnalyses::all();
    }
  };

  // -------------------- Liveness/Reaching (stubs) --------------------

  struct LivenessPass : PassInfoMixin<LivenessPass>
  {
      /**
     * @brief Each set we need to generate for the pass
     */
      struct BlockState
      {
          BitVector in;
          BitVector out;
          BitVector use;
          BitVector def;
      };

      /**
       * @brief The meet function for a union of all the succs for function
       *
       * @param ins Bitvectors for all succs of this node
       * @return BitVector
       */
      static BitVector meetUnion(const std::vector<BitVector>& ins)
      {
          // If its empty the bitwise or will yield nothing
          if (ins.empty())
              return {};
          /* Start with first element and then or each bit with each bit in all other ins*/
          BitVector out = ins[0];
          for (size_t i = 1; i < ins.size(); ++i)
              out |= ins[i];
          return out;
      }

      PreservedAnalyses run(Function& F, FunctionAnalysisManager&)
      {
          outs() << "=== ";
          F.printAsOperand(outs(), false);
          outs() << " ===\n";
          outs() << "[starter] liveness: implement backward dataflow (use/def, IN/OUT)\n";


          /* Fills in the "universe" block with every operand in function */
          std::vector<Value*> universe;
          for (auto& BB : F)
          {
              for (auto& I : BB)
              {
                  if (!I.getType()->isVoidTy())
                  {
                      //if the values aren't constants add them to the vector
                      if (!isa<ConstantInt>(I.getOperand(0)))
                          universe.push_back(I.getOperand(0));
                      if (!isa<ConstantInt>(I.getOperand(1)))
                          universe.push_back(I.getOperand(1));
                      universe.push_back(&I);
                  }
              }
          }
          /* Removes any duplicates from the list */
          std::sort(universe.begin(), universe.end());
          universe.erase(std::unique(universe.begin(), universe.end()), universe.end());

          //Create a vector for backwards traversal through the tree
          DenseMap<const BasicBlock*, BlockState> st;
          std::vector<BasicBlock*> order;
          order.push_back(&F.getEntryBlock());
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
              /* Default out: empty set */
              bs.out = BitVector(universe.size(), false);
              /* Default use: empty set */
              bs.use = BitVector(universe.size(), false);
              /* Default def: empty set */
              bs.def = BitVector(universe.size(), false);

              std::vector<Value*> useVec, defVec;

              for (Instruction& I : *BB)
              {
                  if (!I.getType()->isVoidTy())
                  {
                      /* Gets value of left operator in the universe */
                      {
                          bool alreadyInDef = false;

                          for (int i = 0; i < defVec.size(); i++)
                          {
                              if (defVec[i] == I.getOperand(0))
                                  alreadyInDef = true;
                          }
                          if (!alreadyInDef)
                              useVec.push_back(I.getOperand(0));
                      }
                      /* Gets value of right operator in the universe */
                      {
                          bool alreadyInDef = false;

                          for (int i = 0; i < defVec.size(); i++)
                          {
                              if (defVec[i] == I.getOperand(1))
                                  alreadyInDef = true;
                          }
                          if (!alreadyInDef)
                              useVec.push_back(I.getOperand(1));
                      }

                      //if the instruction is a phi node, check the incoming values
                      if (auto* P = dyn_cast<PHINode>(&I))
                      {
                          for (int i = 0; i < P->getNumIncomingValues(); i++)
                          {
                              bool alreadyInDef = false;

                              for (int i = 0; i < defVec.size(); i++)
                              {
                                  if (defVec[i] == P->getIncomingValue(i))
                                      alreadyInDef = true;
                              }
                              if (!alreadyInDef)
                                  useVec.push_back(P->getIncomingValue(i));
                          }
                      }

                      for (size_t i = 0; i < universe.size(); ++i)
                      {
                          // If the instruction defines a value add it to def
                          if (universe[i] == &I)
                              //bs.def.set(static_cast<unsigned>(i));
                              defVec.push_back(&I);
                      }

                      for (Value* V : defVec)
                      {
                          auto it = std::find(universe.begin(), universe.end(), V);
                          // Add to use if operator matches, isn't end, and isn't already in def
                          if (it != universe.end())
                          {
                              bs.def.set(static_cast<unsigned>(it - universe.begin()));
                          }
                      }

                      for (Value* V : useVec)
                      {
                          auto it = std::find(universe.begin(), universe.end(), V);
                          // Add to use if operator matches, isn't end, and isn't already in def
                          if (it != universe.end())
                          {
                              bs.use.set(static_cast<unsigned>(it - universe.begin()));
                          }
                      }
                  }
              }

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

                  std::vector<BitVector> succIns;

                  //for each successor of our BB, add it to our list of successors to check
                  for (BasicBlock* succ : successors(BB))
                      succIns.push_back(st[succ].in);
                  //if our list of successors is empty, add an empty bitvector
                  if (succIns.empty())
                      succIns.push_back(BitVector(universe.size(), false));

                  //set our out set to the union of all successors
                  st[BB].out = meetUnion(succIns);

                  //calculate our "new" in set with our meet function "use[BB] U (out[BB] - def[BB])"
                  BitVector newIn = st[BB].out;
                  newIn.reset(st[BB].def);
                  newIn |= st[BB].use;

                  //if we have not reached a fixed point, set changed to true to run the loop again
                  if (newIn != st[BB].in)
                  {
                      st[BB].in = newIn;
                      changed = true;
                  }
              }
          }

          /* Nice print for each basic block all the required fields */
          for (BasicBlock* BB : order)
          {
              outs() << "BB: ";
              BB->printAsOperand(outs(), false);
              outs() << "\n";
              printValueBitSet(outs(), "use", st[BB].use, universe);
              printValueBitSet(outs(), "def", st[BB].def, universe);
              printValueBitSet(outs(), "IN", st[BB].in, universe);
              printValueBitSet(outs(), "OUT", st[BB].out, universe);
          }

          return PreservedAnalyses::all();
      }
  };

  struct ReachingPass : PassInfoMixin<ReachingPass>
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
    };

    /**
     * @brief The meet function for a union of all the preds for function
     *
     * @param ins Bitvectors for all preds of this node
     * @return BitVector
     */
    static BitVector meetUnion(const std::vector<BitVector> &ins)
    {
      /* If its empty nothing will intersect */
      if (ins.empty())
        return {};
      /* Start with first element and then and each bit with each bit in all other ins*/
      BitVector out = ins[0];
      for (size_t i = 1; i < ins.size(); ++i)
        out |= ins[i];
      return out;
    }

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &)
    {
      outs() << "=== ";
      F.printAsOperand(outs(), false);
      outs() << " ===\n";
      outs() << "[starter] reaching: implement forward dataflow (gen/kill, IN/OUT)\n";

      /* Fills in the "universe" block with every instruction in function */
      std::vector<Instruction *> universe;
      for (auto &BB : F)
      {
        for (auto &I : BB)
        {
          if (!I.getType()->isVoidTy())
          {
            universe.push_back(&I);
          }
        }
      }

      /* Creating a vector for the order of traversal through the tree */
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

      /* Creates bitvector with every bit set the size of the universe */
      BitVector all(universe.size(), true);
      for (BasicBlock *BB : order)
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

        for (Instruction &I : *BB)
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
        for (BasicBlock *BB : order)
        {
          /* Get pred outs */
          std::vector<BitVector> predOuts;
          /* If starting outs is empty */
          if (BB == &F.getEntryBlock())
            predOuts.push_back(BitVector(universe.size(), false));
          /* Checks all predecessors and add up their outs */
          for (BasicBlock *pred : predecessors(BB))
            predOuts.push_back(st[pred].out);
          /* If predecessors outs was empty push empty bitvector */
          if (predOuts.empty())
            predOuts.push_back(BitVector(universe.size(), false));

          /* Set in to intersection of all previous outs */
          st[BB].in = meetUnion(predOuts);

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

      /* Nice print for each basic block all the required fields */
      for (BasicBlock *BB : order)
      {
        outs() << "BB: ";
        BB->printAsOperand(outs(), false);
        outs() << "\n";
        printBitSet(outs(), "gen", st[BB].gen, universe);
        printBitSet(outs(), "kill", st[BB].kill, universe);
        printBitSet(outs(), "IN", st[BB].in, universe);
        printBitSet(outs(), "OUT", st[BB].out, universe);
      }
      return PreservedAnalyses::all();
    }
  };

  // -------------------- Constant Propagation 3-point (starter) --------------------

  struct ConstantPropPass : PassInfoMixin<ConstantPropPass>
  {
    enum class Kind
    {
      Top,
      Const,
      Bottom
    }; // Top=unknown, Bottom=NAC

    struct LVal
    {
      Kind kind = Kind::Top;
      int64_t c = 0;
      static LVal top() { return {Kind::Top, 0}; }
      static LVal constant(int64_t v) { return {Kind::Const, v}; }
      static LVal bottom() { return {Kind::Bottom, 0}; }
      bool operator==(const LVal &o) const { return kind == o.kind && c == o.c; }
      bool operator!=(const LVal &o) const { return !(*this == o); }
    };

    using CPState = DenseMap<const Value *, LVal>;
    struct BlockState
    {
      CPState in;
      CPState out;
    };

    static LVal meetVal(LVal a, LVal b)
    {
      if (a.kind == Kind::Top)
        return b;
      if (b.kind == Kind::Top)
        return a;
      if (a.kind == Kind::Bottom || b.kind == Kind::Bottom)
        return LVal::bottom();
      return (a.c == b.c) ? a : LVal::bottom();
    }

    static LVal evalValue(const Value *V, const CPState &st)
    {
      if (const auto *CI = dyn_cast<ConstantInt>(V))
        return LVal::constant(CI->getSExtValue());
      auto it = st.find(V);
      if (it == st.end())
        return LVal::top();
      return it->second;
    }

    static LVal evalBinary(const BinaryOperator &BO, const CPState &st)
    {
      LVal l = evalValue(BO.getOperand(0), st);
      LVal r = evalValue(BO.getOperand(1), st);
      if (l.kind != Kind::Const || r.kind != Kind::Const)
        return LVal::top();

      // Starter example: only Add is implemented.
      // TODO(student): extend to Sub/Mul/Div and policy for unsupported ops.
      if (BO.getOpcode() == Instruction::Add)
        return LVal::constant(l.c + r.c);
      return LVal::top();
    }

    static LVal evalPhi(const PHINode &Phi, const DenseMap<const BasicBlock *, BlockState> &states)
    {
      (void)Phi;
      (void)states;
      // TODO(student): merge incoming values from predecessor OUT states.
      return LVal::top();
    }

    static CPState transferBlock(BasicBlock &BB, const CPState &in,
                                 const DenseMap<const BasicBlock *, BlockState> &states)
    {
      CPState out = in;
      for (Instruction &I : BB)
      {
        if (I.getType()->isVoidTy())
          continue;

        if (auto *P = dyn_cast<PHINode>(&I))
        {
          out[&I] = evalPhi(*P, states);
        }
        else if (auto *BO = dyn_cast<BinaryOperator>(&I))
        {
          out[&I] = evalBinary(*BO, out);
        }
        else
        {
          // TODO(student): handle icmp/select/loads/stores etc.
          out[&I] = LVal::top();
        }
      }
      return out;
    }

    static bool sameState(const CPState &a, const CPState &b, const std::vector<const Value *> &domain)
    {
      for (const Value *V : domain)
      {
        LVal av = a.lookup(V);
        LVal bv = b.lookup(V);
        if (av != bv)
          return false;
      }
      return true;
    }

    static void printState(raw_ostream &OS, StringRef label, const CPState &st,
                           const std::vector<const Value *> &domain, bool showTop = false)
    {
      OS << "  " << label << ": { ";
      bool first = true;
      for (const Value *V : domain)
      {
        LVal v = st.lookup(V);
        if (!showTop && v.kind == Kind::Top)
          continue;
        if (!first)
          OS << "; ";
        first = false;
        /* If value is null return null as string */
        if (!V)
            return "(null)";
        /* If value has name update to str and add % */
        if (V->hasName())
            return "%" + V->getName().str();
        /* If value is a constant interger return string of int */
        if (const auto* C = dyn_cast<ConstantInt>(V))
            return std::to_string(C->getSExtValue());
        /* If all those scenarios fail just print to screen maybe ?*/
        std::string S;
        raw_string_ostream OS(S);
        V->printAsOperand(OS, false);
        return S;
    }