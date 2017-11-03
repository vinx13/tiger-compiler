#ifndef __SEMANT_H_
#define __SEMANT_H_

#include "absyn.h"
#include "symbol.h"
#include "types.h"

typedef void* Tr_exp;
typedef struct expty_tag
{
	Tr_exp exp; 
	Ty_ty ty;
} expty;

expty transVar(S_table venv, S_table tenv, A_var v);
expty transExp(S_table venv, S_table tenv, A_exp a);
void		 transDec(S_table venv, S_table tenv, A_dec d);
Ty_ty		 transTy (              S_table tenv, A_ty a);

void SEM_transProg(A_exp exp);

#endif
