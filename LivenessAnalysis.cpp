#include <string>
#include <map>
#include <iostream>
#include <fstream>
#include <set>

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

namespace {
struct LivenessAnalysis : public FunctionPass {
    string func_name = "test";
    static char ID;
    LivenessAnalysis() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
        errs() << "Liveness Analysis Pass: ";
        errs() << F.getName() <<"\n";
        /*
        IN[B]: Variables live at B’s entry.
        OUT[B]: Variables live at B’s exit.
        GEN[B]: Variables that are used in B prior to their definition in B.
        KILL[B]: Variables definitely assigned value in B before any use of that variable in B.
        */
        std::map<const BasicBlock *, std::set<const StringRef>> IN;
        std::map<const BasicBlock *, std::set<const StringRef>> OUT;
        std::map<const BasicBlock *, std::set<const StringRef>> GEN;
        std::map<const BasicBlock *, std::set<const StringRef>> KILL;

        /*
         -- Initialize sets:
         for every block B
            IN[B] = GEN[B]  //(GEN[B]: Variables that are used in B prior to their definition in B.
            OUT[B] = φ
         */
        for (auto &basic_block : F) {
            auto &gen = GEN[&basic_block];
            auto &in = IN[&basic_block];
            auto &out = OUT[&basic_block];
            auto &kill = KILL[&basic_block];
            for (const auto &inst : basic_block) {
                //travers instructions
                // use by +, -, *, /, br
                if(inst.getOpcode() == Instruction::Add || inst.getOpcode() == Instruction::Sub
                || inst.getOpcode() == Instruction::Mul || inst.getOpcode() == Instruction::SDiv
                || inst.getOpcode()==Instruction::PHI || inst.getOpcode()==Instruction::ICmp
                || inst.getOpcode()==Instruction::Load || inst.getOpcode() == Instruction::Store){
                    for(int i = 0; i<inst.getNumOperands();i++){
                        auto var = inst.getOperand(i)->getName();
                        if(inst.getOpcode() != Instruction::Store && (i != 1)){
                            if(kill.count(var)==0){
                                gen.insert(var);
                            }
                        }else{
                            kill.insert(var);
                        }
                    }
                }else {
                    for(int i = 0; i<inst.getNumOperands();i++) {
                        auto var = inst.getOperand(i)->getName();
                        kill.insert(var);
                    }
                }
            }
            std::copy(gen.begin(),gen.end(),std::inserter(in,in.begin()));
            errs()<<"initialized IN[] "<<basic_block.getName();
            for(auto it : IN[&basic_block]){
                errs()<<" "<<it;
            }
            errs()<<"\n";


        }//end of all blocks
    /*
    -- Iteratively solve equations:
    change = true;
    while change {
        change = false;
        for each B ≠ Be {
        OLDIN = IN[B]
        OUT[B] =    s ε succ(B)  U(IN[S])
        IN[B] = GEN[B] U (OUT[B] – KILL[B])
        if IN[B] ≠ OLDIN then change = true
     }
    }
    */
        const auto &bbs = F.getBasicBlockList();
        auto entry = bbs.begin();
        for (const auto &inst : *entry){

        }

        bool change = true;
        while(change){
            change = false;
            for(auto it = bbs.rbegin(); it!=bbs.rend();it++){
                auto &bb= *it;
                auto old_in = IN[&bb];
                auto old_out = OUT[&bb];
                IN[&bb].clear(); OUT[&bb].clear();
                auto &new_in = IN[&bb];
                auto &new_out = OUT[&bb];
                auto kill = KILL[&bb];
                auto gen = GEN[&bb];
                //        OUT[B] =    s ε succ(B)  U(IN[S])
                //        IN[B] = GEN[B] U (OUT[B] – KILL[B])
                for(const BasicBlock *succ : llvm::successors(&bb)){
                    auto succ_out = OUT[succ];
                    auto succ_in = IN[succ];
                    std::set_union(succ_in.begin(), succ_in.end(),
                                   new_out.begin(), new_out.end(), std::inserter(new_out, new_out.begin()));
                }// get OUT[B]
                auto out_diff_kill = std::set<const StringRef>();
                std::set_difference(new_out.begin(),new_out.end(),
                                    kill.begin(),kill.end(),std::inserter(out_diff_kill, out_diff_kill.begin()));
                std::set_union(gen.begin(),gen.end(),
                               out_diff_kill.begin(),out_diff_kill.end(),std::inserter(new_in, new_in.begin()));
                if(new_in != old_in){
                    change = true;
                }
            }
        }

        //print out result
        for(auto &bb:F){
            if(IN.count(&bb)){
                errs()<<bb.getName()<<" IN :";
                for(auto it : IN[&bb]){
                    errs()<<" "<<it;
                }
            }
            errs()<<"\n";


            if(OUT.count(&bb)){
                errs()<<bb.getName()<<" OUT :";
                for(auto it : OUT[&bb]){
                    if(it.contains("i")){
                        continue;
                    }
                    errs()<<" "<<it;
                }
            }
            errs()<<"\n\n";
        }

    } //end of runonfunction
}; // end of struct LivenessAnalysis
}  // end of anonymous namespace

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("LivenessAnalysis", "LivenessAnalysis Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
