// ECE/CS 5544 Assignment 2 starter unifiedpass.cpp
// Lean starter: buildable scaffolds, minimal solved logic.

#include <algorithm>
#include <cstdint>
#include <numeric>
#include <string>
#include <vector>

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

namespace {

std::string getShortValueName(const Value* V) {
  if (!V) return "(null)";
  if (V->hasName()) return "%" + V->getName().str();
  if (const auto* C = dyn_cast<ConstantInt>(V)) return std::to_string(C->getSExtValue());
  std::string S;
  raw_string_ostream OS(S);
  V->printAsOperand(OS, false);
  return S;
}

// -------------------- Available Expressions (starter) --------------------

struct Expr {
  Instruction::BinaryOps opcode;
  Value* lhs;
  Value* rhs;
  auto operator<=>(const Expr&) const = default;

  static Expr fromBO(const BinaryOperator& BO) {
    return {BO.getOpcode(), BO.getOperand(0), BO.getOperand(1)};
  }
};

raw_ostream& operator<<(raw_ostream& OS, const Expr& E) {
  OS << getShortValueName(E.lhs) << " ";
  switch (E.opcode) {
    case Instruction::Add: OS << "+"; break;
    case Instruction::Sub: OS << "-"; break;
    case Instruction::Mul: OS << "*"; break;
    case Instruction::SDiv:
    case Instruction::UDiv: OS << "/"; break;
    default: OS << "(op)"; break;
  }
  OS << " " << getShortValueName(E.rhs);
  return OS;
}

template <typename T>
void printBitSet(raw_ostream& OS, StringRef label, const BitVector& bits, const std::vector<T>& universe) {
  OS << "  " << label << ": { ";
  bool first = true;
  for (unsigned i = 0; i < bits.size(); ++i) {
    if (!bits.test(i)) continue;
    if (!first) OS << "; ";
    first = false;
    OS << universe[i];
  }
  OS << " }\n";
}

struct AvailablePass : PassInfoMixin<AvailablePass> {
  struct BlockState {
    BitVector in;
    BitVector out;
    BitVector gen;
    BitVector kill;
  };

  static BitVector meetIntersect(const std::vector<BitVector>& ins) {
    if (ins.empty()) return {};
    BitVector out = ins[0];
    for (size_t i = 1; i < ins.size(); ++i) out &= ins[i];
    return out;
  }

  PreservedAnalyses run(Function& F, FunctionAnalysisManager&) {
    outs() << "=== ";
    F.printAsOperand(outs(), false);
    outs() << " ===\n";

    std::vector<Expr> universe;
    for (auto& BB : F) {
      for (auto& I : BB) {
        if (auto* BO = dyn_cast<BinaryOperator>(&I)) universe.push_back(Expr::fromBO(*BO));
      }
    }
    std::sort(universe.begin(), universe.end());
    universe.erase(std::unique(universe.begin(), universe.end()), universe.end());

    DenseMap<const BasicBlock*, BlockState> st;
    std::vector<BasicBlock*> order;
    order.push_back(&F.getEntryBlock());
    for (size_t i = 0; i < order.size(); ++i) {
      for (BasicBlock* succ : successors(order[i])) {
        if (std::find(order.begin(), order.end(), succ) == order.end()) order.push_back(succ);
      }
    }

    BitVector all(universe.size(), true);
    for (BasicBlock* BB : order) {
      BlockState bs;
      bs.in = BitVector(universe.size(), false);
      bs.out = all;
      bs.gen = BitVector(universe.size(), false);
      bs.kill = BitVector(universe.size(), false);

      for (Instruction& I : *BB) {
        if (auto* BO = dyn_cast<BinaryOperator>(&I)) {
          Expr e = Expr::fromBO(*BO);
          auto it = std::lower_bound(universe.begin(), universe.end(), e);
          if (it != universe.end() && *it == e) bs.gen.set(static_cast<unsigned>(it - universe.begin()));
        }
        if (!I.getType()->isVoidTy()) {
          for (size_t i = 0; i < universe.size(); ++i) {
            if (universe[i].lhs == &I || universe[i].rhs == &I) bs.kill.set(static_cast<unsigned>(i));
          }
        }
      }

      BitVector notGen = bs.gen;
      bs.kill &= notGen.flip();
      st[BB] = bs;
    }

    bool changed = true;
    while (changed) {
      changed = false;
      for (BasicBlock* BB : order) {
        std::vector<BitVector> predOuts;
        if (BB == &F.getEntryBlock()) predOuts.push_back(BitVector(universe.size(), false));
        for (BasicBlock* pred : predecessors(BB)) predOuts.push_back(st[pred].out);
        if (predOuts.empty()) predOuts.push_back(BitVector(universe.size(), false));

        st[BB].in = meetIntersect(predOuts);

        // TODO(student): implement transfer OUT = GEN U (IN - KILL).
        BitVector newOut = st[BB].in;

        if (newOut != st[BB].out) {
          st[BB].out = newOut;
          changed = true;
        }
      }
    }

    for (BasicBlock* BB : order) {
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

struct LivenessPass : PassInfoMixin<LivenessPass> {
  PreservedAnalyses run(Function& F, FunctionAnalysisManager&) {
    outs() << "=== ";
    F.printAsOperand(outs(), false);
    outs() << " ===\n";
    outs() << "[starter] liveness: implement backward dataflow (use/def, IN/OUT)\n";
    return PreservedAnalyses::all();
  }
};

struct ReachingPass : PassInfoMixin<ReachingPass> {
  PreservedAnalyses run(Function& F, FunctionAnalysisManager&) {
    outs() << "=== ";
    F.printAsOperand(outs(), false);
    outs() << " ===\n";
    outs() << "[starter] reaching: implement forward dataflow (gen/kill, IN/OUT)\n";
    return PreservedAnalyses::all();
  }
};

// -------------------- Constant Propagation 3-point (starter) --------------------

struct ConstantPropPass : PassInfoMixin<ConstantPropPass> {
  enum class Kind { Top, Const, Bottom };  // Top=unknown, Bottom=NAC

  struct LVal {
    Kind kind = Kind::Top;
    int64_t c = 0;
    static LVal top() { return {Kind::Top, 0}; }
    static LVal constant(int64_t v) { return {Kind::Const, v}; }
    static LVal bottom() { return {Kind::Bottom, 0}; }
    bool operator==(const LVal& o) const { return kind == o.kind && c == o.c; }
    bool operator!=(const LVal& o) const { return !(*this == o); }
  };

  using CPState = DenseMap<const Value*, LVal>;
  struct BlockState {
    CPState in;
    CPState out;
  };

  static LVal meetVal(LVal a, LVal b) {
    if (a.kind == Kind::Top) return b;
    if (b.kind == Kind::Top) return a;
    if (a.kind == Kind::Bottom || b.kind == Kind::Bottom) return LVal::bottom();
    return (a.c == b.c) ? a : LVal::bottom();
  }

  static LVal evalValue(const Value* V, const CPState& st) {
    if (const auto* CI = dyn_cast<ConstantInt>(V)) return LVal::constant(CI->getSExtValue());
    auto it = st.find(V);
    if (it == st.end()) return LVal::top();
    return it->second;
  }

  static LVal evalBinary(const BinaryOperator& BO, const CPState& st) {
    LVal l = evalValue(BO.getOperand(0), st);
    LVal r = evalValue(BO.getOperand(1), st);
    if (l.kind != Kind::Const || r.kind != Kind::Const) return LVal::top();

    // Starter example: only Add is implemented.
    // TODO(student): extend to Sub/Mul/Div and policy for unsupported ops.
    if (BO.getOpcode() == Instruction::Add) return LVal::constant(l.c + r.c);
    return LVal::top();
  }

  static LVal evalPhi(const PHINode& Phi, const DenseMap<const BasicBlock*, BlockState>& states) {
    (void)Phi;
    (void)states;
    // TODO(student): merge incoming values from predecessor OUT states.
    return LVal::top();
  }

  static CPState transferBlock(BasicBlock& BB, const CPState& in,
                               const DenseMap<const BasicBlock*, BlockState>& states) {
    CPState out = in;
    for (Instruction& I : BB) {
      if (I.getType()->isVoidTy()) continue;

      if (auto* P = dyn_cast<PHINode>(&I)) {
        out[&I] = evalPhi(*P, states);
      } else if (auto* BO = dyn_cast<BinaryOperator>(&I)) {
        out[&I] = evalBinary(*BO, out);
      } else {
        // TODO(student): handle icmp/select/loads/stores etc.
        out[&I] = LVal::top();
      }
    }
    return out;
  }

  static bool sameState(const CPState& a, const CPState& b, const std::vector<const Value*>& domain) {
    for (const Value* V : domain) {
      LVal av = a.lookup(V);
      LVal bv = b.lookup(V);
      if (av != bv) return false;
    }
    return true;
  }

  static void printState(raw_ostream& OS, StringRef label, const CPState& st,
                         const std::vector<const Value*>& domain, bool showTop = false) {
    OS << "  " << label << ": { ";
    bool first = true;
    for (const Value* V : domain) {
      LVal v = st.lookup(V);
      if (!showTop && v.kind == Kind::Top) continue;
      if (!first) OS << "; ";
      first = false;
      V->printAsOperand(OS, false);
      if (v.kind == Kind::Const) OS << " = " << v.c;
      else if (v.kind == Kind::Bottom) OS << " = NAC";
      else OS << " = TOP";
    }
    OS << " }\n";
  }

  PreservedAnalyses run(Function& F, FunctionAnalysisManager&) {
    outs() << "=== ";
    F.printAsOperand(outs(), false);
    outs() << " ===\n";

    std::vector<const Value*> domain;
    for (auto& BB : F) {
      for (auto& I : BB) {
        if (!I.getType()->isVoidTy()) domain.push_back(&I);
      }
    }

    std::vector<BasicBlock*> order;
    order.push_back(&F.getEntryBlock());
    for (size_t i = 0; i < order.size(); ++i) {
      for (BasicBlock* succ : successors(order[i])) {
        if (std::find(order.begin(), order.end(), succ) == order.end()) order.push_back(succ);
      }
    }

    DenseMap<const BasicBlock*, BlockState> st;
    for (BasicBlock* BB : order) {
      BlockState bs;
      for (const Value* V : domain) {
        bs.in[V] = LVal::top();
        bs.out[V] = LVal::top();
      }
      st[BB] = std::move(bs);
    }

    bool changed = true;
    while (changed) {
      changed = false;
      for (BasicBlock* BB : order) {
        CPState newIn;
        for (const Value* V : domain) newIn[V] = LVal::top();

        bool hasPred = false;
        for (BasicBlock* pred : predecessors(BB)) {
          hasPred = true;
          for (const Value* V : domain) newIn[V] = meetVal(newIn.lookup(V), st[pred].out.lookup(V));
        }
        if (!hasPred) {
          for (const Value* V : domain) newIn[V] = LVal::top();
        }

        st[BB].in = newIn;
        CPState newOut = transferBlock(*BB, newIn, st);
        if (!sameState(st[BB].out, newOut, domain)) {
          st[BB].out = std::move(newOut);
          changed = true;
        }
      }
    }

    for (BasicBlock* BB : order) {
      outs() << "BB: ";
      BB->printAsOperand(outs(), false);
      outs() << "\n";
      printState(outs(), "IN", st[BB].in, domain);
      printState(outs(), "OUT", st[BB].out, domain);
    }

    return PreservedAnalyses::all();
  }
};

}  // namespace

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "UnifiedPass", "v0.3-starter", [](PassBuilder& PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager& FPM,
                   ArrayRef<PassBuilder::PipelineElement>) -> bool {
                  if (Name == "available") {
                    FPM.addPass(AvailablePass());
                    return true;
                  }
                  if (Name == "liveness") {
                    FPM.addPass(LivenessPass());
                    return true;
                  }
                  if (Name == "reaching") {
                    FPM.addPass(ReachingPass());
                    return true;
                  }
                  if (Name == "constantprop") {
                    FPM.addPass(ConstantPropPass());
                    return true;
                  }
                  return false;
                });
          }};
}
