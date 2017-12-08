#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"
#include "assem.h"

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
    S_symbol name;
    F_accessList formals;
    F_accessList locals;
    int argSize;
    int length;
    Temp_tempList calleesaves;
    Temp_tempList callersaves;
    Temp_tempList specialregs;
};

static Temp_tempList specialRegs = NULL;
static Temp_tempList callerSaveRegs = NULL;
static Temp_tempList calleeSaveRegs = NULL;
static Temp_tempList argRegs = NULL;

static Temp_temp eax, ebx, ecx, edx, esi, edi, esp, ebp;

Temp_temp F_eax() { return eax; }
Temp_temp F_edx() { return edx; }
Temp_temp F_esp() { return esp; }
Temp_temp F_ebp() { return ebp; }
Temp_temp F_ebx() { return ebx; }
Temp_temp F_esi() { return esi; }
Temp_temp F_edi() { return edi; }


Temp_label F_name(F_frame f) {
    return f->name;
}

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
    return ebp;
}

Temp_temp F_RV(void) {
    return eax;
}

Temp_temp F_SP(void) {
    return esp;
}

const int F_wordSize = 4;
const int F_numReg = 8;

T_exp F_Exp(F_access f, T_exp framePtr) {
    if (f->kind == inFrame) {
        return T_Mem(T_Binop(T_plus, framePtr, T_Const(f->u.offset)));
    }
    return T_Temp(f->u.reg);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm) {
    return stm;
}

AS_instrList F_procEntryExit2(AS_instrList body) { 
    static Temp_tempList returnSink = NULL;
    if (!returnSink)
        returnSink = Temp_TempList(esp, Temp_TempList(F_FP(), NULL));
    return AS_splice(body, AS_InstrList(AS_Oper("#exit2", NULL, returnSink, NULL), NULL));
}

AS_proc F_procEntryExit3(F_frame frame, AS_instrList body) {
    char prolog[256];
    sprintf(prolog, "# exit3\n"
                    "push %%ebp\n"
                    "movl %%esp, %%ebp\n"
                    "subl $%d, %%esp\n",
                frame->length);
    char *epilog = "leave\nret\n";
    return AS_Proc(String(prolog), body, epilog); 
}

T_exp F_externalCall(string s, T_expList args) {
    string name = (string)checked_malloc(strlen(s)+2);
    name[0] = '_';
    strcpy(name, s);
    return T_Call(T_Name(Temp_namedlabel(name)), args);
}

F_accessList F_formals(F_frame f) {
    return f->formals;
}

F_frame F_newFrame(Temp_label name, U_boolList formalEscapes) {
    F_frame f = checked_malloc(sizeof(*f));
    F_accessList formals = F_AccessList(NULL, NULL), tail = formals;
    f->name = name;
    f->length = 12;
    int count = 0;
    for (; formalEscapes; formalEscapes = formalEscapes->tail) {
        bool escape = formalEscapes->head;
        F_access f_access;
        if (escape) {
            ++count;
            f_access = InFrame((1+count) * F_wordSize);
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

int F_allocInStack(F_frame frame) {
    frame->length += F_wordSize;
   return -frame->length; 
}

F_access F_allocLocal(F_frame frame, bool escape) {
    if (escape) {
        F_access access = InFrame(F_allocInStack(frame));
        return access;
    }
    printf("alloc in reg\n");
    return InReg(Temp_newtemp());
}

Temp_tempList F_callerSaveRegs() {
    static Temp_tempList inst;
    if (!inst) inst = Temp_TempList(eax, Temp_TempList(ecx, Temp_TempList(edx, NULL)));
    return inst;
}

Temp_tempList F_calleeSaveRegs() {
    static Temp_tempList inst;
    if (!inst) inst = Temp_TempList(ebx, Temp_TempList(edi, Temp_TempList(esi, NULL)));
    return inst;
}

void F_init(void) {
    eax = Temp_newtemp();
    ebx = Temp_newtemp();
    ecx = Temp_newtemp();
    edx = Temp_newtemp();
    esi = Temp_newtemp();
    ebp = Temp_newtemp();
    esp = Temp_newtemp();
    edi = Temp_newtemp();
}

Temp_map F_regTempMap(void) {
    static Temp_map map = NULL; 
    if (!map) {
        map = Temp_empty();
        Temp_enter(map, eax, "\%eax");
        Temp_enter(map, ebx, "\%ebx");
        Temp_enter(map, ecx, "\%ecx");
        Temp_enter(map, edx, "\%edx");
        Temp_enter(map, ebp, "\%ebp");
        Temp_enter(map, esp, "\%esp");
        Temp_enter(map, edi, "\%edi");
        Temp_enter(map, esi, "\%esi");
    }
    return map;
}

Temp_tempList F_getRegList(void) {
    static Temp_tempList inst = NULL;
    if (!inst) inst = 
    Temp_TempList(eax,
    Temp_TempList(ebx,
    Temp_TempList(ecx,
    Temp_TempList(edx,
    Temp_TempList(esi,
    Temp_TempList(edi,
    Temp_TempList(esp,
    Temp_TempList(ebp,
    NULL))))))));

    return inst;
}

int F_frameSize(F_frame f) {
    return f->length;
}


