#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ {
    Tr_access head;
    struct Tr_accessList_ *tail;
} *Tr_accessList;

typedef struct Tr_level_ *Tr_level;

typedef struct Tr_expList_{
    Tr_exp head;
    struct Tr_expList_ *tail;
} *Tr_expList;

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label label, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

// var
Tr_exp Tr_simpleVar(Tr_access, Tr_level);

Tr_exp Tr_fieldVar(Tr_exp, int);

Tr_exp Tr_subscriptVar(Tr_exp, Tr_exp);

// exp
Tr_exp Tr_nilExp();

Tr_exp Tr_intExp(int);

Tr_exp Tr_recordExp(Tr_expList);

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init);

Tr_exp Tr_stringCompare(A_oper, Tr_exp, Tr_exp);

Tr_exp Tr_opExp(A_oper, Tr_exp, Tr_exp);

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init);

Tr_exp Tr_ifExp(Tr_exp, Tr_exp, Tr_exp);

Tr_exp Tr_forExp(Tr_exp, Tr_exp, Tr_exp, Tr_exp, Temp_label done);

Tr_exp Tr_whileExp(Tr_exp, Tr_exp, Temp_label done);

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals, bool isProc);

Tr_exp Tr_stringExp(string);

Tr_exp Tr_seqExp(Tr_expList, bool);

Tr_exp Tr_assignExp(Tr_exp, Tr_exp);

Tr_exp Tr_breakExp(Temp_label done);

Tr_exp Tr_callExp(Temp_label, Tr_expList, Tr_level, Tr_level);

Tr_exp Tr_letExp(Tr_expList, Tr_exp);

Tr_exp Tr_Nop();

#endif
