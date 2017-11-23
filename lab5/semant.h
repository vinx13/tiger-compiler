#ifndef __SEMANT_H_
#define __SEMANT_H_

#include "absyn.h"
#include "symbol.h"
#include "types.h"
#include "frame.h"
#include "translate.h"

typedef struct expty_tag
{
	Tr_exp exp; 
	Ty_ty ty;
} expty;

expty transVar(S_table venv, S_table tenv, Tr_level level, A_var v);
expty transExp(S_table venv, S_table tenv, Tr_level level, A_exp a);
Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, A_dec d);
Ty_ty transTy (S_table tenv, A_ty a);

F_fragList SEM_transProg(A_exp exp);

#endif
