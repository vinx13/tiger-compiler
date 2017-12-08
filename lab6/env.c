#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "env.h" 

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Tr_access access, Ty_ty ty)
{
	E_enventry entry = checked_malloc(sizeof(*entry));

	entry->u.var.access = access;
	entry->u.var.ty = ty;
	return entry;
}

E_enventry E_ROVarEntry(Tr_access access, Ty_ty ty)
{
	E_enventry entry = checked_malloc(sizeof(*entry));

	entry->u.var.access = access;
	entry->u.var.ty = ty;
	entry->readonly = 1;
	return entry;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result)
{
	E_enventry entry = checked_malloc(sizeof(*entry));

	entry->u.fun.level = level;
	entry->u.fun.label = label;
	entry->u.fun.formals = formals;
	entry->u.fun.result = result ? result : Ty_Void();
	return entry;
}

//sym->value
//type_id(name, S_symbol) -> type (Ty_ty)
S_table E_base_tenv(void)
{
	S_table table;
	S_symbol ty_int;
	S_symbol ty_string;

	table = S_empty();

	//basic type: string
	ty_int = S_Symbol("int");
	S_enter(table, ty_int, Ty_Int());	

	//basic type: string
	ty_string = S_Symbol("string");
	S_enter(table, ty_string, Ty_String());	

	return table;
}


void declareFunc(S_table env, string name, Ty_tyList formals, Ty_ty result) {
    S_enter(env, S_Symbol(name), E_FunEntry(Tr_outermost(), Temp_namedlabel(name), formals, result));
}

S_table E_base_venv(void)
{
	S_table venv = S_empty();
	Ty_tyList formals;
	
    declareFunc(venv, "flush", NULL, Ty_Void());
    declareFunc(venv, "exit", Ty_TyList(Ty_Int(), NULL), Ty_Void());	
    declareFunc(venv, "not", Ty_TyList(Ty_Int(), NULL), Ty_Int());
    declareFunc(venv, "printi", Ty_TyList(Ty_Int(), NULL), Ty_Void());
    declareFunc(venv, "chr", Ty_TyList(Ty_Int(), NULL), Ty_String());
    declareFunc(venv, "getchar", NULL, Ty_String());
    declareFunc(venv, "print", Ty_TyList(Ty_String(), NULL), Ty_Void());
    declareFunc(venv, "ord", Ty_TyList(Ty_String(), NULL), Ty_Int());
    declareFunc(venv, "size", Ty_TyList(Ty_String(), NULL), Ty_Int());
	declareFunc(venv, "concat", Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String());
	declareFunc(venv, "substring", Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(), Ty_TyList(Ty_Int(), NULL))), Ty_String());

	return venv;
}
