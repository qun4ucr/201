#include <string>
#include <map>
#include <iostream>
#include <fstream>
#include <set>
#include <vector>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/User.h"


using namespace llvm;
using namespace std;

struct my_exp {
    string op1;
    string op2;
    unsigned int opcode;
    string op;

    my_exp(StringRef _op1, unsigned int _op, StringRef _op2) {
        this->op1 = _op1.str();
        this->op2 = _op2.str();
        this->opcode = _op;

        switch (_op) {
            case Instruction::Add:
                this->op = "+";
                break;
            case Instruction::Mul:
                this->op = "*";
                break;
            case Instruction::SDiv:
                this->op = "/";
                break;
            case Instruction::Sub:
                this->op = "-";
                break;
            default:
                break;
        }
    }

    string getExp() const {
        return op1 + " " + op + " " + op2 + "\n";
    }


    friend bool operator<(const my_exp &a, const my_exp &b) {
        return a.opcode < b.opcode;
    }
};

namespace {
    struct LivenessAnalysis : public FunctionPass {
        string func_name = "test";
        static char ID;

        LivenessAnalysis() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            errs() << "Liveness Analysis Pass: ";
            errs() << F.getName() << "\n";
            /*
            IN[B]: Expressions available at B’s entry.
            OUT[B]: Expressions available at B’s exit.
            GEN[B]: Expressions computed within B that are available at the end of B.
            KILL[B]: Expressions whose operands are redefined in B.
             */
            std::map<const BasicBlock *, std::vector<const struct my_exp *>> GEN;
            std::map<const BasicBlock *, std::vector<const struct my_exp *>> KILL;
            std::map<const BasicBlock *, std::vector<const struct my_exp *>> IN;
            std::map<const BasicBlock *, std::vector<const struct my_exp *>> OUT;

            // i_xx -> a/b/c/d/...
            std::map<StringRef, StringRef> REF;

            for (auto &basic_block: F) {
                auto &gen = GEN[&basic_block];
                auto &kill = KILL[&basic_block];

                for (const auto &inst: basic_block) {
                    //travers instructions
                    // use by +, -, *, /, br
                    if (inst.getOpcode() == Instruction::Add || inst.getOpcode() == Instruction::Sub
                        || inst.getOpcode() == Instruction::Mul || inst.getOpcode() == Instruction::SDiv) {
                        auto op1 = REF[inst.getOperand(0)->getName()];
                        auto op2 = REF[inst.getOperand(1)->getName()];
                        auto op = inst.getOpcode();
                        auto *_exp = new my_exp(op1, op, op2);
                        gen.push_back(_exp);

                    } else if (inst.getOpcode() == Instruction::Load) {
                        auto a = dyn_cast_or_null<Value>(&inst);
                        if (!a) {
                            continue;
                        }
                        auto i_name = a->getName();
                        auto Var_name = inst.getOperand(0)->getName();
                        REF[i_name] = Var_name;
                    } else if (inst.getOpcode() == Instruction::Store) {
                        auto re_var = inst.getOperand(1)->getName().str();
                        //errs()<<"re defined here  "<<re_var<<"\n";
                        for (auto _exp: gen) {
                            if (_exp->op1 == re_var || _exp->op2 == re_var) {
                                kill.push_back(_exp);
                            }
                        }
                    }
                }

            }//end of all blocks
            /*
             -- Initialize sets:
            IN[Bs] = φ;   OUT[Bs] = GEN[Bs];
            for every block B ≠ Bs
                OUT[B] = All Expressions;
            */



            /*
            -- Iteratively solve equations:
            change = true;
            While change {
            change = false;
            for each B ≠ Bs {
                OLDOUT = OUT[B]
                IN[B] =    p ε pred(B) OUT[P]
                OUT[B] = GEN[B] U (IN[B] – KILL[B])
                if OUT[B] ≠ OLDOUT then change = true
                }
            }
            */


            //print out result
            for (auto &bb: F) {
                if (GEN.count(&bb)) {
                    errs() << bb.getName() << " GEN :";
                    for (auto it: GEN[&bb]) {
                        errs() << it->getExp();
                    }
                }
                errs() << "\n";
            }

        } //end of runonfunction
    }; // end of struct LivenessAnalysis
}  // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "LivenessAnalysis Pass",
                                        false /* Only looks at CFG */,
                                        false /* Analysis Pass */);
