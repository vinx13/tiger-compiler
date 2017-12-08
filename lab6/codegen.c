#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"
#include "tree.h"
#include "x86frame.h"

//Lab 6: put your code here
static AS_instrList instrList, cur;
static Temp_temp savedEbx, savedEsi, savedEdi;

static void emit(AS_instr inst) {
    if (!instrList) instrList = cur = AS_InstrList(inst, NULL);
    else cur = cur->tail = AS_InstrList(inst, NULL);
}

static Temp_temp munchExp(T_exp);

static void munchStm(T_stm s);

static Temp_tempList munchArgs(int i, T_expList args) {
    if (!args) return NULL;
    Temp_tempList right = munchArgs(i + 1, args->tail);
    Temp_temp left = munchExp(args->head);
    emit(AS_Oper("pushl `s0", Temp_TempList(F_SP(), NULL), Temp_TempList(left, Temp_TempList(F_SP(), NULL)), NULL));
    return Temp_TempList(left, right);
}

static void saveCallerRegs(void) {
    Temp_tempList regs = F_callerSaveRegs();
    int offset = -4;
    for (; regs; regs = regs->tail) {
        Temp_temp reg = regs->head;
        char buf[64];
        sprintf(buf, "movl `s0, %d(`s1)", offset);
        emit(AS_Oper(buf, NULL, Temp_TempList(reg, Temp_TempList(F_FP(), NULL)), NULL));
        offset -= F_wordSize;
    }
}

static void saveCalleeRegs(void) {
    savedEbx = Temp_newtemp();
    savedEdi = Temp_newtemp();
    savedEsi = Temp_newtemp();
    emit(AS_Move("movl `s0, `d0", Temp_TempList(savedEbx, NULL), Temp_TempList(F_ebx(), NULL)));
    emit(AS_Move("movl `s0, `d0", Temp_TempList(savedEdi, NULL), Temp_TempList(F_edi(), NULL)));
    emit(AS_Move("movl `s0, `d0", Temp_TempList(savedEsi, NULL), Temp_TempList(F_esi(), NULL)));
}

static void restoreCalleeRegs0(Temp_tempList regs) {
    if (!regs) return;
    Temp_temp head = regs->head;
    restoreCalleeRegs0(regs->tail);
    emit(AS_Oper("popl `d0", Temp_TempList(head, Temp_TempList(F_SP(), NULL)), Temp_TempList(F_SP(), NULL), NULL));
}


static void restoreCallerRegs(void) {
    Temp_tempList regs = F_callerSaveRegs();
    int offset = -4;
    for (; regs; regs = regs->tail) {
        Temp_temp reg = regs->head;
        char buf[64];
        sprintf(buf, "movl %d(`s0), `d0", offset);
        emit(AS_Oper(buf, Temp_TempList(reg, NULL), Temp_TempList(F_FP(), NULL), NULL));
        offset -= F_wordSize;
    }
}

static void restoreCalleeRegs(void) {
    emit(AS_Move("movl `s0, `d0", Temp_TempList(F_ebx(), NULL), Temp_TempList(savedEbx, NULL)));
    emit(AS_Move("movl `s0, `d0", Temp_TempList(F_edi(), NULL), Temp_TempList(savedEdi, NULL)));
    emit(AS_Move("movl `s0, `d0", Temp_TempList(F_esi(), NULL), Temp_TempList(savedEsi, NULL)));

}

static Temp_temp munchOpExp(T_exp e) {
    Temp_temp left = munchExp(e->u.BINOP.left), right = munchExp(e->u.BINOP.right);
    Temp_temp r = Temp_newtemp();

    if (e->u.BINOP.op == T_div) {
        Temp_tempList divident = Temp_TempList(F_eax(), Temp_TempList(F_edx(), NULL));
        emit(AS_Move("movl `s0, `d0", Temp_TempList(F_eax(), NULL), Temp_TempList(left, NULL)));
        emit(AS_Oper("cltd", divident, Temp_TempList(F_eax(), NULL), AS_Targets(NULL)));
        emit(AS_Oper("idivl `s0", divident,
                     Temp_TempList(right, divident), AS_Targets(NULL))
        );
        emit(AS_Move("movl `s0, `d0", Temp_TempList(r, NULL), Temp_TempList(F_eax(), NULL)));
        return r;
    } else if (e->u.BINOP.op == T_mul) {
        emit(AS_Move("movl `s0, `d0", Temp_TempList(F_eax(), NULL), Temp_TempList(left, NULL)));
        emit(AS_Oper("imul `s0", Temp_TempList(F_edx(), Temp_TempList(F_eax(), NULL)),
                     Temp_TempList(right, Temp_TempList(F_eax(), NULL)), NULL));
        emit(AS_Move("movl `s0, `d0", Temp_TempList(r, NULL), Temp_TempList(F_eax(), NULL)));
        return r;
    }

    emit(AS_Move("movl `s0, `d0", Temp_TempList(r, NULL), Temp_TempList(left, NULL)));
    char *op;
    switch (e->u.BINOP.op) {
        case T_plus:
            op = "addl";
            break;
        case T_minus:
            op = "subl";
            break;
        case T_lshift:
            assert(0);
            op = "sall";
            break;
        default:
            assert(0);
            break; // unreachable
    }
    char buf[256];
    tprintf(buf, "%s `s0, `d0", op);
    emit(AS_Oper(buf, Temp_TempList(r, NULL), Temp_TempList(right, Temp_TempList(r, NULL)), NULL));

    return r;
}

int Temp_tempListLength(Temp_tempList l) {
    if (!l) return 0;
    return Temp_tempListLength(l->tail) + 1;
}


static Temp_temp munchExp(T_exp e) {
    char buf[256];
    switch (e->kind) {
        case T_TEMP: {
            return e->u.TEMP;
        }
        case T_CONST: {
            Temp_temp r = Temp_newtemp();
            tprintf(buf, "movl $%d, `d0", e->u.CONST);
            emit(AS_Oper(buf, Temp_TempList(r, NULL), NULL, NULL));
            return r;
        }
        case T_NAME: {
            Temp_temp r = Temp_newtemp();
            tprintf(buf, "movl $%s, `d0", Temp_labelstring(e->u.NAME));
            emit(AS_Oper(buf, Temp_TempList(r, NULL), NULL, NULL));
            return r;
        }
        case T_CALL: {
            assert(e->u.CALL.fun->kind == T_NAME);
            Temp_temp r = Temp_newtemp(), rv = F_RV();
            string func = Temp_labelstring(e->u.CALL.fun->u.NAME);
            T_expList args = e->u.CALL.args;
            Temp_tempList argTemps = munchArgs(0, args);
            int length = Temp_tempListLength(argTemps);
            saveCallerRegs();
            tprintf(buf, "call %s", func);
            emit(AS_Oper(buf, Temp_TempList(F_eax(), NULL)/*F_callerSaveRegs()*/, NULL, AS_Targets(NULL)));
            if (length) {
                memset(buf, 0, sizeof(buf));
                sprintf(buf, "addl $%d, `d0", F_wordSize * length);
                emit(AS_Oper(buf, Temp_TempList(F_SP(), NULL), NULL, NULL));
            }
            emit(AS_Move("movl `s0, `d0", Temp_TempList(r, NULL), Temp_TempList(rv, NULL)));
            restoreCallerRegs();
            return r;
        }
        case T_MEM: {
            Temp_temp r = Temp_newtemp();
            T_exp src = e->u.MEM;
            if (src->kind == T_CONST) {
                tprintf(buf, "movl %d, `d0", src->u.CONST);
                emit(AS_Oper(buf, Temp_TempList(r, NULL), NULL, NULL));
                return r;
            } else if (src->kind == T_BINOP) {
                if (src->u.BINOP.op == T_plus && src->u.BINOP.right->kind == T_CONST) {
                    Temp_temp base = munchExp(src->u.BINOP.left);
                    int offset = src->u.BINOP.right->u.CONST;
                    tprintf(buf, "movl %d(`s0), `d0", offset);
                    emit(AS_Oper(buf, Temp_TempList(r, NULL), Temp_TempList(base, NULL), NULL));
                    return r;
                }
                if (src->u.BINOP.op == T_plus && src->u.BINOP.right->kind == T_BINOP &&
                    src->u.BINOP.right->u.BINOP.op == T_lshift) {
                    assert(src->u.BINOP.right->u.BINOP.right->kind == T_CONST);
                    assert(src->u.BINOP.right->u.BINOP.right->u.CONST == 2);
                    Temp_temp base = munchExp(src->u.BINOP.left);
                    Temp_temp index = munchExp(src->u.BINOP.right->u.BINOP.left);
                    tprintf(buf, "movl (`s0, `s1, 4), `d0");
                    emit(AS_Oper(buf, Temp_TempList(r, NULL), Temp_TempList(base, Temp_TempList(index, NULL)), NULL));
                    return r;
                }
            }
            Temp_temp s = munchExp(e->u.MEM);
            tprintf(buf, "movl (`s0), `d0");
            emit(AS_Move(buf, Temp_TempList(r, NULL), Temp_TempList(s, NULL)));
            return r;
        }
        case T_ESEQ: { // FIXME: is this reachable ?
            munchStm(e->u.ESEQ.stm);
            return munchExp(e->u.ESEQ.exp);
        }
        case T_BINOP: {
            return munchOpExp(e);
        }
        default:
            assert(0);
            break;
    }
}

static void munchMoveStm(T_stm s) {
    char buf[256];
    T_exp dst = s->u.MOVE.dst;
    T_exp src = s->u.MOVE.src;


    if (dst->kind == T_TEMP && src->kind == T_TEMP) {
        emit(AS_Move("movl `s0, `d0", Temp_TempList(dst->u.TEMP, NULL), Temp_TempList(src->u.TEMP, NULL)));
        return;
    }
    Temp_temp left = munchExp(s->u.MOVE.src);

    if (dst->kind == T_TEMP) {
        emit(AS_Move("movl `s0, `d0", Temp_TempList(dst->u.TEMP, NULL), Temp_TempList(left, NULL)));
        return;
    }

    assert (dst->kind == T_MEM);
    dst = dst->u.MEM;
    if (dst->kind == T_BINOP) {
        if (dst->u.BINOP.op == T_plus && dst->u.BINOP.right->kind == T_CONST) {
            Temp_temp base = munchExp(dst->u.BINOP.left);
            int offset = dst->u.BINOP.right->u.CONST;
            tprintf(buf, "movl `s0, %d(`s1)", offset);
            emit(AS_Oper(buf, NULL, Temp_TempList(left, Temp_TempList(base, NULL)), NULL));
            return;
        }
        if (dst->u.BINOP.op == T_plus && dst->u.BINOP.right->kind == T_BINOP &&
            dst->u.BINOP.right->u.BINOP.op == T_lshift) {
            assert(dst->u.BINOP.right->u.BINOP.right->kind == T_CONST);
            assert(dst->u.BINOP.right->u.BINOP.right->u.CONST == 2);
            Temp_temp base = munchExp(dst->u.BINOP.left);
            Temp_temp index = munchExp(dst->u.BINOP.right->u.BINOP.left);
            tprintf(buf, "movl `s0, (`s1, `s2, 4)");
            emit(AS_Oper(buf, NULL, Temp_TempList(left, Temp_TempList(base, Temp_TempList(index, NULL))), NULL));
            return;
        }
    }
    Temp_temp right = munchExp(dst);
    emit(AS_Oper("movl `s0, (`s1)", NULL, Temp_TempList(left, Temp_TempList(right, NULL)), NULL));

}

static void munchStm(T_stm s) {
    char buf[256];
    switch (s->kind) {
        case T_MOVE: {
            munchMoveStm(s);
            break;
        }
        case T_LABEL: {
            Temp_label label = s->u.LABEL;
            tprintf(buf, "%s:", Temp_labelstring(label));
            emit(AS_Label(buf, label));
            break;
        }
        case T_EXP: {
            munchExp(s->u.EXP);
            break;
        }
        case T_SEQ: {
            munchStm(s->u.SEQ.left);
            munchStm(s->u.SEQ.right);
            break;
        }
        case T_NOP:
            break;
        case T_CJUMP: {
            Temp_temp left = munchExp(s->u.CJUMP.left), right = munchExp(s->u.CJUMP.right);
            tprintf(buf, "cmp `s1, `s0");
            emit(AS_Oper(buf, NULL, Temp_TempList(left, Temp_TempList(right, NULL)), AS_Targets(NULL)));
            char *op;
            switch (s->u.CJUMP.op) {
                case T_eq:
                    op = "je";
                    break;
                case T_ne:
                    op = "jne";
                    break;
                case T_lt:
                    op = "jl";
                    break;
                case T_le:
                    op = "jle";
                    break;
                case T_gt:
                    op = "jg";
                    break;
                case T_ge:
                    op = "jge";
                    break;
                case T_ult:
                    op = "jb";
                    break;
                case T_ule:
                    op = "jbe";
                    break;
                case T_ugt:
                    op = "ja";
                    break;
                case T_uge:
                    op = "jae";
                    break;
            }
            memset(buf, 0, sizeof(buf));
            tprintf(buf, "%s `j0", op);
            emit(AS_Oper(buf, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));

            break;

        }
        case T_JUMP: {
            assert(s->u.JUMP.exp->kind == T_NAME);
            Temp_label target = s->u.JUMP.exp->u.NAME;
            tprintf(buf, "jmp `j0");
            emit(AS_Oper(buf, NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
            break;
        }
        default:
            assert(0);
            break;
    }
}


AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    AS_instrList list;

    {
        T_stmList prev = stmList, cur = prev->tail;
        while (cur) {
            if (cur->head->kind == T_NOP) {
                prev->tail = cur->tail;
                cur = cur->tail;
            } else {
                prev = cur;
                cur = cur->tail;
            }
        }
    }


    instrList = cur = NULL;
    emit(AS_Oper("", Temp_TempList(F_ebp(), Temp_TempList(F_esp(), NULL)), NULL, NULL));
    saveCalleeRegs();
    for (; stmList; stmList = stmList->tail) {
        munchStm(stmList->head);
    }
    restoreCalleeRegs();
    return F_procEntryExit2(instrList);
}

