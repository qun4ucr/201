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
        this->op1 = min(_op1.str(),_op2.str());
        this->op2 = max(_op1.str(),_op2.str());
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
        return this->op1 + " " + this->op + " " + this->op2;
    }

    friend bool operator<(const my_exp &a, const my_exp &b) {
        return a.getExp() < b.getExp();
    }

    friend bool operator==(const my_exp &a, const my_exp &b) {
        return a.getExp() == b.getExp();
    }
};

namespace {
    struct AvailableAnalysis : public FunctionPass {
        string func_name = "test";
        static char ID;

        AvailableAnalysis() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            errs() << "AvailExpression: "<< F.getName() << "\n";
            /*
            IN[B]: Expressions available at B’s entry.
            OUT[B]: Expressions available at B’s exit.
            GEN[B]: Expressions computed within B that are available at the end of B.
            KILL[B]: Expressions whose operands are redefined in B.
             */
            std::set<const struct my_exp > allEXP;
            std::map<const BasicBlock *, std::set<const struct my_exp >> GEN;
            std::map<const BasicBlock *, std::set<const struct my_exp >> KILL;
            std::map<const BasicBlock *, std::set<const struct my_exp >> IN;
            std::map<const BasicBlock *, std::set<const struct my_exp >> OUT;

            // i_xx -> a/b/c/d/...
            std::map<StringRef, StringRef> REF;

            for (auto &basic_block: F) {
                auto &gen = GEN[&basic_block];
                for (const auto &inst: basic_block) {
                    //travers instructions
                    // use by +, -, *, /
                    if (inst.getOpcode() == Instruction::Add || inst.getOpcode() == Instruction::Sub
                        || inst.getOpcode() == Instruction::Mul || inst.getOpcode() == Instruction::SDiv) {
                        auto op1 = REF[inst.getOperand(0)->getName()];
                        auto op2 = REF[inst.getOperand(1)->getName()];
                        auto op = inst.getOpcode();
                        auto *_exp = new my_exp(op1, op, op2);
                        gen.insert(*_exp);
                        allEXP.insert(*_exp);
                    } else if (inst.getOpcode() == Instruction::Load) {
                        auto a = dyn_cast_or_null<Value>(&inst);
                        if (!a) {
                            continue;
                        }
                        auto i_name = a->getName();
                        auto Var_name = inst.getOperand(0)->getName();
                        REF[i_name] = Var_name;
                    }
                } // end of all inst
            //errs()<<"\n\n";
            }//end of all blocks
            for (auto &basic_block: F) {
                auto &kill = KILL[&basic_block];
                for (const auto &inst: basic_block) {
                    if (inst.getOpcode() == Instruction::Store) {
                        auto re_var = inst.getOperand(1)->getName().str();
                        //errs()<<"re defined here  "<<re_var<<"\n";
                        for (auto _exp: allEXP) {
                            //errs() << _exp->op1 << _exp->op2 <<"KILLing??";
                            if (_exp.op1 == re_var || _exp.op2 == re_var) {
                                //errs() << re_var << "KILLing";
                                kill.insert(_exp);
                            }
                        }
                    }
                }
            } //end of 2nd bb loop

            /*
             -- Initialize sets:
            IN[Bs] = φ;   OUT[Bs] = GEN[Bs];
            for every block B ≠ Bs
                OUT[B] = All Expressions;
            */
            int bb_counter = 0;
            for (auto &basic_block: F) {
                bb_counter ++;
                auto &gen = GEN[&basic_block];
                auto &out = OUT[&basic_block];
                if(bb_counter == 1){
                    std::copy(gen.begin(),gen.end(),std::inserter(out,out.begin()));
                }else{
                    std::copy(allEXP.begin(),allEXP.end(),std::inserter(out,out.begin()));
                }
            }

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
            const auto &bbs = F.getBasicBlockList();
            bool change = true;
            while(change){
                change = false;
                for(auto it = bbs.begin(); it!=bbs.end();it++) {
                    auto &bb = *it;
                    auto old_out = OUT[&bb];
                    OUT[&bb].clear();IN[&bb].clear();
                    auto &in = IN[&bb];
                    set<const my_exp> new_in;
                    auto &new_out = OUT[&bb];
                    auto kill = KILL[&bb];
                    auto gen = GEN[&bb];
                    //                IN[B] =    p ε pred(B) OUT[P]
                    int pred_count = 0;
                    for(const BasicBlock *pred : llvm::predecessors(&bb)){
                        pred_count++;
                        auto pred_out = OUT[pred];
                        if(pred_count==1){
                            std::copy(pred_out.begin(), pred_out.end(),std::inserter(in, in.begin()));
                        }else{
                            std::set_intersection(pred_out.begin(), pred_out.end(),
                                                  in.begin(), in.end(), std::inserter(new_in, new_in.begin()));
                            in.clear();
                            std::copy(new_in.begin(), new_in.end(),std::inserter(in, in.begin()));
                        }
                    }// get IN[B]
                    //                OUT[B] = GEN[B] U (IN[B] – KILL[B])
                    set<const my_exp> diff;
                    std::set_difference(in.begin(),in.end(),kill.begin(),kill.end(),
                                        std::inserter(diff, diff.begin()));
                    std::set_union(gen.begin(),gen.end(),diff.begin(),diff.end(),
                                             std::inserter(new_out, new_out.begin()));
                    if(old_out != new_out){
                        change = true;
                    }
                }
            }

            //print out result
            for (auto &bb: F) {
                errs() << "------"<<bb.getName()<<"-----";
                /*
                errs()<< " \nGEN :\n";
                for (auto it: GEN[&bb]) {
                    errs() << it.getExp() << " ";
                }
                errs()<< " \nKILL :\n";
                for (auto it: KILL[&bb]) {
                    errs() << it.getExp() << " ";
                }
                errs()<< " \nIN :\n";
                for (auto it: IN[&bb]) {
                    errs() << it.getExp() << " ";
                }*/
                errs()<< " \nAvailable :";
                for (auto it: OUT[&bb]) {
                    errs() << it.getExp() << "    ";
                }
                errs()<< "\n";
            }
            return true;
        } //end of runonfunction
    }; // end of struct AvailableAnalysis
}  // end of anonymous namespace

char AvailableAnalysis::ID = 0;
static RegisterPass<AvailableAnalysis> X("AvailableAnalysis", "AvailableAnalysis Pass",
                                        false /* Only looks at CFG */,
                                        false /* Analysis Pass */);
