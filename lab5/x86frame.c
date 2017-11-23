#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/

//varibales
struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

struct Tr_level_ {
    F_frame f;
    int level;
};

struct F_frame_ {
    Temp_label name;
    F_accessList formals;
    F_accessList locals;
    int argSize;
    int length;
    Temp_tempList calleesaves;
    Temp_tempList callersaves;
    Temp_tempList specialregs;
};

static F_accessList F_AccessList(F_access head, F_accessList tail) {
    F_accessList p = (F_accessList)checked_malloc(sizeof(*p));
    p->head = head;
    p->tail = tail;

    return p;
}

static F_access InFrame(int offset) {
    F_access f = (F_access)checked_malloc(sizeof(*f));
    f->kind = inFrame;
    f->u.offset = offset; 

    return f;
}

static F_access InReg(Temp_temp reg) {
    F_access f = (F_access)checked_malloc(sizeof(*f));
    f->kind = inReg;
    f->u.reg = reg;

    return f;
}

F_frag F_StringFrag(Temp_label label, string str) {   
    F_frag p = (F_frag)checked_malloc(sizeof(*p));
    p->kind = F_stringFrag;
    p->u.stringg.label = label;
    p->u.stringg.str = str;

    return p;
}
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {        
    F_frag p = (F_frag)checked_malloc(sizeof(*p));
    p->kind = F_procFrag;
    p->u.proc.body = body;
    p->u.proc.frame = frame;

    return p;
}                                                     
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
    F_fragList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;

    return list;
}                                                     

Temp_temp F_FP(void) {
    return Temp_newtemp();
}

Temp_temp F_RV(void) {
    return Temp_newtemp();
}

const int F_wordSize = 4;

T_exp F_Exp(F_access f, T_exp framePtr) {
    if (f->kind == inFrame) {
        return T_Mem(T_Binop(T_plus, framePtr, T_Const(f->u.offset)));
    }
    return T_Temp(f->u.reg);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm) {
    return stm;
}

T_exp F_externalCall(string s, T_expList args) {
    return T_Call(T_Name(Temp_namedlabel(s)), args);
}

F_accessList F_formals(F_frame f) {
    return f->formals;
}

F_frame F_newFrame(Temp_label name, U_boolList formalEscapes) {
    F_frame f = checked_malloc(sizeof(*f));
    F_accessList formals = F_AccessList(NULL, NULL), tail = formals;
    f->name = name;

    int count = 0;
    for (; formalEscapes; formalEscapes = formalEscapes->tail) {
        bool escape = formalEscapes->head;
        F_access f_access;
        if (escape) {
            ++count;
            f_access = InFrame(count * F_wordSize);
        } else {
            f_access = InReg(Temp_newtemp());
        }
        tail = tail->tail = F_AccessList(f_access, NULL); 
    }

    F_accessList old = formals;
    formals = formals->tail;
    free(old);

    f->formals = formals;

    return f;
}

F_access F_allocLocal(F_frame frame, bool escape) {
    if (escape) {
        F_access access = InFrame(-frame->length);
        frame->length += F_wordSize;
        return access;
    }
    return InReg(Temp_newtemp());
}
