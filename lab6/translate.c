#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.

static F_fragList frags, cur;


struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
};

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

Tr_access Tr_Access(Tr_level level, F_access access) {
    Tr_access p = (Tr_access)checked_malloc(sizeof(*p));
    p->level = level;
    p->access = access;

    return p;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail) {
    Tr_accessList p = (Tr_accessList)checked_malloc(sizeof(*p));
    p->head = head;
    p->tail = tail;

    return p;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
    Tr_expList p = (Tr_expList)checked_malloc(sizeof(*p));
    p->head = head;
    p->tail = tail;

    return p;
}

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
    do {
		*(tList->head) = label;
    } while ((tList = tList->tail));
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

static Tr_exp Tr_Ex(T_exp ex) {
    Tr_exp e = checked_malloc(sizeof(*e));
    e->kind = Tr_ex;
    e->u.ex = ex;
    
    return e;
}

static Tr_exp Tr_Nx(T_stm nx) {
    Tr_exp e = checked_malloc(sizeof(*e));
    e->kind = Tr_nx;
    e->u.nx = nx;

    return e;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) {
    Tr_exp e = checked_malloc(sizeof(*e));
    e->kind = Tr_cx;
    e->u.cx.trues = trues;
    e->u.cx.falses = falses;
    e->u.cx.stm = stm;
    
    return e;
}

static T_exp unEx(Tr_exp e) {
    switch (e->kind) {
    case Tr_ex:
        return e->u.ex;
    case Tr_cx: {
        Temp_temp r = Temp_newtemp();
        Temp_label t = Temp_newlabel(), f = Temp_newlabel();
        doPatch(e->u.cx.trues, t);
        doPatch(e->u.cx.falses, f);
        return T_Eseq(  T_Move(T_Temp(r), T_Const(1)),
                T_Eseq(e->u.cx.stm,
                    T_Eseq(T_Label(f),
                        T_Eseq(T_Move(T_Temp(r), T_Const(0)),
                            T_Eseq(T_Label(t),
                                T_Temp(r))))));
    }
    case Tr_nx:
        return T_Eseq(e->u.nx, T_Const(0));
    }
    // unreachable
}

static T_stm unNx(Tr_exp e) {
    // TODO
    switch(e->kind) {
    case Tr_ex:
        return T_Exp(e->u.ex);
    case Tr_nx:
        return e->u.nx;
    case Tr_cx:
        // TODO
    default:
        break; // unreachable
    }
    return NULL;
}

static struct Cx unCx(Tr_exp e) {
    // TODO
    struct Cx result;
    return result;
}

static void addFrag(F_frag frag) {
    if (!frags) {
        cur = frags = F_FragList(frag, NULL);
    } else {
        cur = cur->tail = F_FragList(frag, NULL);
    }
}

Tr_level Tr_outermost(void) {
    static Tr_level outermost = NULL;
    if (!outermost) {
        outermost = Tr_newLevel(NULL, Temp_newlabel(), NULL);
    }
    return outermost;
}

static Tr_level Tr_Level(Tr_level parent, F_frame frame) {
    Tr_level level = checked_malloc(sizeof(*level));
    level->parent = parent;
    level->frame = frame;
    return level;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) {
    if (parent)
        formals = U_BoolList(1, formals);
    
    F_frame frame = F_newFrame(name, formals);
    Tr_level level = Tr_Level(parent, frame);

    return level;
}

Tr_accessList Tr_formals(Tr_level level) {
    F_accessList formals = F_formals(level->frame)->tail; // skip static link
    
    if (!formals) return NULL;
    Tr_accessList accessList = Tr_AccessList(NULL, NULL), tail = accessList;
    do {
        tail = tail->tail = Tr_AccessList(Tr_Access(level, formals->head), NULL);
    } while ((formals = formals->tail));
    
    Tr_accessList old = accessList;
    accessList = accessList->tail;
    free(old);
    
    return accessList;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape) {
    F_access f_access = F_allocLocal(level->frame, escape);
    return Tr_Access(level, f_access);
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level) {
    T_exp fp = T_Temp(F_FP());
    while (level != access->level) {
        fp = F_Exp(F_formals(level->frame)->head, fp);
        level = level->parent;
    }
    return Tr_Ex(F_Exp(access->access, T_Temp(F_FP())));
}

Tr_exp Tr_fieldVar(Tr_exp record, int nth) {
    T_exp addr = T_Binop(T_plus, unEx(record), T_Const(nth*4));
    return Tr_Ex(T_Mem(addr));
}

Tr_exp Tr_subscriptVar(Tr_exp array, Tr_exp index) {
    T_exp offset = T_Binop(T_lshift, unEx(index), T_Const(2));
    T_exp addr = T_Binop(T_plus, unEx(array), offset);
    return Tr_Ex(T_Mem(addr));
    
}

Tr_exp Tr_nilExp() {
    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_intExp(int n) {
    return Tr_Ex(T_Const(n));
}

Tr_exp Tr_stringExp(string s) {
    Temp_label label = Temp_newlabel();
    F_frag frag = F_StringFrag(label, s);
    addFrag(frag); 
    return Tr_Ex(T_Name(label));
}

Tr_exp Tr_opExp(A_oper op, Tr_exp tr_left, Tr_exp tr_right) {
    T_exp left = unEx(tr_left), right = unEx(tr_right);
    
    // arithmetic
    if (op == A_plusOp) {
        return Tr_Ex(T_Binop(T_plus, left, right));
    } else if (op == A_minusOp) {
        return Tr_Ex(T_Binop(T_minus, left, right));
    } else if (op == A_timesOp) {
        return Tr_Ex(T_Binop(T_mul, left, right));
    } else if (op == A_divideOp) {
        return Tr_Ex(T_Binop(T_div, left, right));
    }

    // compare
    T_stm stm;
    // TODO strings
    if (op == A_eqOp) {
        stm = T_Cjump(T_eq, left, right, NULL, NULL);
    } else if (op == A_ltOp) {
        stm = T_Cjump(T_lt, left, right, NULL, NULL);
    } else if (op == A_leOp) {
        stm = T_Cjump(T_le, left, right, NULL, NULL);
    } else if (op == A_gtOp) {
        stm = T_Cjump(T_gt, left, right, NULL, NULL);
    } else if (op == A_geOp) {
        stm = T_Cjump(T_ge, left, right, NULL, NULL);
    } else if (op == A_neqOp) {
        stm = T_Cjump(T_ne, left, right, NULL, NULL);
    }
    return Tr_Cx(NULL, NULL, stm);
}

Tr_exp Tr_recordExp(Tr_expList exps) {
    // is empty record legal ? in this case exps is null
    return Tr_Ex(NULL);         
}  

Tr_exp Tr_seqExp(Tr_expList exps) {
    if (!exps) return NULL;
    if (!exps->tail) return exps->head;
    T_stm seq = T_Seq(unNx(exps->head), unNx(exps->tail->head));
    T_stm cur = seq;
    exps = exps->tail->tail;
    for (; exps; exps = exps->tail) {
        // replace cur.right with a new seq
        cur->u.SEQ.right = T_Seq(cur->u.SEQ.right, unNx(exps->head));
    }

    return Tr_Nx(seq);
}

Tr_exp Tr_assignExp(Tr_exp dest, Tr_exp value) {
    return Tr_Nx(T_Move(unEx(dest), unEx(value)));
}

Tr_exp Tr_callExp(Temp_label func, Tr_exp args) {
   return Tr_Nop(); 
}

Tr_exp Tr_forExp(Tr_exp cond, Tr_exp lo, Tr_exp hi, Tr_exp body) {
    T_exp hi_ = T_Temp(Temp_newtemp());
    Temp_label done = Temp_newlabel(), loop = Temp_newlabel();

    return Tr_Nx(
    T_Seq( T_Move(unEx(cond), unEx(lo)),
    T_Seq( T_Move(hi_, unEx(hi)),
    T_Seq( T_Cjump(T_gt, unEx(cond), hi_, done, loop),
    T_Seq( T_Label(loop),
    T_Seq( unNx(body),
    T_Seq( T_Move(unEx(cond), T_Binop(T_plus, unEx(cond), T_Const(1))),
    T_Seq( T_Cjump(T_le, unEx(cond), hi_, loop, done),
           T_Label(done)
       ))))))));
}

Tr_exp Tr_whileExp(Tr_exp cond, Tr_exp body) {
    Temp_label done = Temp_newlabel(), loop = Temp_newlabel();
   
    return Tr_Nx(NULL); // TODO

}

Tr_exp Tr_ifExp(Tr_exp cond, Tr_exp then, Tr_exp elsee) {
    return Tr_Nx(NULL); // TODO

}

void Tr_funcDec() {
    
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals) {
    F_frag frag = F_ProcFrag(unNx(body), level->frame);  
    // TODO
    addFrag(frag);
}


Tr_exp Tr_Nop() {
    return Tr_Ex(T_Const(0));
}

F_fragList Tr_getResult() {
    return frags;
}
