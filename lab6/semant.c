#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"
#include "translate.h"
#include "stack.h"

#define isUniqueElmt(T_ELMT) isUniqueElmt_##T_ELMT
#define _MAKE_UNIQUE_ELMT_FUNC(T_ELMT) \
bool isUniqueElmt(T_ELMT)(T_ELMT##List types, T_ELMT ty) {   \
    int count = 0;                                  \
    for(; types; types = types->tail) {             \
        T_ELMT cur = types->head;                   \
        if (cur->name == ty->name) count++;         \
    }                                               \
    return count == 1;                              \
}                                                   

_MAKE_UNIQUE_ELMT_FUNC(A_namety)
#define isUniqueTyName isUniqueElmt(A_namety)
_MAKE_UNIQUE_ELMT_FUNC(A_fundec)
#define isUniqueFuncName isUniqueElmt(A_fundec)
/*Lab4: Your implementation of lab4*/


static Stack *loopStack; // loop stack

Temp_label startLoop() {
    Temp_label label = Temp_newlabel();
    Stack_Push(loopStack, (void *)label);
    return label;
}

void endLoop() {
    Stack_Pop(loopStack);
}

void startCall() {
    Stack_Push(loopStack, NULL);
}

void endCall() {
    Stack_Pop(loopStack);
}

Temp_label currentLoop() {
    return Stack_Top(loopStack);
}

//In Lab4, the first argument exp should always be **NULL**.
expty expTy(Tr_exp exp, Ty_ty ty)
{
	expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty actual_ty(Ty_ty ty) {
    if (ty->kind != Ty_name) return ty;
    return actual_ty(ty->u.name.ty);
}

int Ty_hasCycle(Ty_ty ty) {
    if (ty->kind != Ty_name) return FALSE;
    Ty_ty cur;
    for (cur = ty->u.name.ty; cur->kind == Ty_name && cur->u.name.ty /* named type may be incomplete */; cur = cur->u.name.ty) {
        if (cur == ty) return TRUE;
    }
    return FALSE;
}

Ty_ty S_checkedLookTy(S_table tenv, S_symbol s, int pos) {
    Ty_ty ty = S_look(tenv, s);
    if (!ty) {
        EM_error(pos, "undefined type %s", S_name(s));
    }
    return ty;
}

E_enventry S_checkedLookVar(S_table venv, S_symbol s, int pos) {
    E_enventry entry = S_look(venv, s);
    if (!entry) {
        EM_error(pos, "undefined variable %s", S_name(s));
    }
    return entry;
}

E_enventry S_checkedLookFunc(S_table venv, S_symbol s, int pos) {
    E_enventry entry = S_look(venv, s);
    if (!entry) {
        EM_error(pos, "undefined function %s", S_name(s));
    }
    return entry;
}

bool S_isEmpty(S_symbol s) {
    return !s || s == S_Symbol("");
}

bool Ty_isSame(Ty_ty ty1, Ty_ty ty2) {
    Ty_ty actual1 = actual_ty(ty1), actual2 = actual_ty(ty2);
    return actual1 == actual2;
}

bool Ty_isCompatible(Ty_ty ty1, Ty_ty ty2) {
    Ty_ty actual1 = actual_ty(ty1), actual2 = actual_ty(ty2);
    if (actual1 == actual2) return TRUE;
    if (actual1->kind == Ty_nil || actual2->kind == Ty_nil) {
        Ty_ty other;
        if (actual1->kind == Ty_nil) 
            other = actual2;
        else 
            other = actual1;
        if (other->kind == Ty_record || other->kind == Ty_array) {
            return TRUE;
        } else {
            return FALSE;
        }
    }
    if (actual1->kind != actual2->kind) return FALSE;

    // no need to check record or array type
    return TRUE;
}

bool Ty_isInt(Ty_ty ty) {
    return Ty_isSame(ty, Ty_Int());
}

bool Ty_isVoid(Ty_ty ty) {
    return Ty_isSame(ty, Ty_Void());
}

bool Ty_isString(Ty_ty ty) {
    return ty->kind == Ty_string;
}

expty transSimpleVar(S_table venv, S_table tenv, Tr_level level, A_var v) {
    E_enventry x = S_look(venv,v->u.simple);
    if (x && x->kind==E_varEntry) {
        Tr_access access = x->u.var.access;
        Tr_exp tr_exp = Tr_simpleVar(access, level);
        return expTy(tr_exp, actual_ty(x->u.var.ty));
    } else {
        EM_error(v->pos,"undefined variable %s", S_name(v->u.simple));
        return expTy(NULL,Ty_Int());
    }
}

expty transFieldVar(S_table venv, S_table tenv, Tr_level level, A_var v) {
    A_var rec = v->u.field.var;
    S_symbol field_name = v->u.field.sym;

    expty rec_meta = transVar(venv, tenv, level, rec);
    Ty_ty ty_rec = actual_ty(rec_meta.ty);

    if (ty_rec->kind != Ty_record) {
        EM_error(v->pos, "not a record type");
        return expTy(NULL, Ty_Int());
    }
    Ty_fieldList fields = ty_rec->u.record;
    
    // search through field list
    Ty_field field = NULL;
    int offset = 0;
    while (fields) {
        if (fields->head->name == field_name) {
            field = fields->head;
            break;
        }
        ++offset;
        fields = fields->tail;
    }
    if (!field) { // not found
        EM_error(v->pos, "field %s doesn't exist", S_name(field_name));
        return expTy(NULL, Ty_Int());
    }

    Tr_exp tr_exp = Tr_fieldVar(rec_meta.exp, offset);
    return expTy(tr_exp, actual_ty(field->ty));
}

expty transSubscriptVar(S_table venv, S_table tenv, Tr_level level, A_var v) {
    A_var arr = v->u.subscript.var;
    A_exp idx = v->u.subscript.exp;
    expty arr_meta = transVar(venv, tenv, level, arr);
    expty idx_meta = transExp(venv, tenv, level, idx);
    
    // check arr
    if (arr_meta.ty->kind != Ty_array) {
        EM_error(v->pos, "array type required");
        return expTy(NULL, Ty_Int());
    }
    // check idx
    if (!Ty_isInt(idx_meta.ty)) {
        EM_error(v->pos, "invalid subscript type");
        return expTy(NULL, Ty_Int());
    }

    Tr_exp tr_exp = Tr_subscriptVar(arr_meta.exp, idx_meta.exp);
    return expTy(tr_exp, actual_ty(arr_meta.ty->u.array));
}

expty transVar(S_table venv, S_table tenv, Tr_level level, A_var v) {
    switch(v->kind) {
    case A_simpleVar: 
        return transSimpleVar(venv, tenv, level, v);
    case A_fieldVar: 
        return transFieldVar(venv, tenv, level, v);
    case A_subscriptVar:
        return transSubscriptVar(venv, tenv, level, v);
    default: break; // unreachable
    }
}

expty transNilExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    return expTy(Tr_nilExp(), Ty_Nil());
}

expty transIntExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    return expTy(Tr_intExp(a->u.intt), Ty_Int());
}

expty transStringExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    return expTy(Tr_stringExp(a->u.stringg), Ty_String());
}

expty transCallExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    S_symbol func_name = a->u.call.func;
    E_enventry func_entry = S_checkedLookFunc(venv, func_name, a->pos);

    if (!func_entry) {
        return expTy(NULL, Ty_Void());
    }
    
    A_expList args = a->u.call.args;
    Ty_tyList ty_formals = func_entry->u.fun.formals;
    Ty_ty ty_result = func_entry->u.fun.result; 

    Tr_expList tr_args = Tr_ExpList(NULL, NULL), cur = tr_args;

    while (ty_formals && args) { 
        A_exp arg = args->head;
        Ty_ty ty_formal = ty_formals->head;
        expty arg_meta = transExp(venv, tenv, level, arg);
        if (!Ty_isSame(ty_formal, arg_meta.ty)) {
            EM_error(arg->pos, "para type mismatch");
        }
        ty_formals = ty_formals->tail;
        cur = cur->tail = Tr_ExpList(arg_meta.exp, NULL);
        args = args->tail;
    }
        
    if (args || ty_formals) {
            EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
    }

    Tr_expList old = tr_args; tr_args = tr_args->tail; free(old);

    startCall();
    Tr_exp tr_exp = Tr_callExp(func_entry->u.fun.label, tr_args, func_entry->u.fun.level, level);
    
    endCall();

    return expTy(tr_exp, func_entry->u.fun.result);
}

expty transOpExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    A_oper oper = a->u.op.oper;
    expty left_meta = transExp(venv, tenv, level, a->u.op.left);
    expty right_meta = transExp(venv, tenv, level, a->u.op.right);

    if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
        if (left_meta.ty->kind != Ty_int) {
            EM_error(a->u.op.left->pos, "integer required");
        }
        if (right_meta.ty->kind != Ty_int) {
            EM_error(a->u.op.right->pos,"integer required");
        }
    } else { // cmp ops
        if (!Ty_isCompatible(left_meta.ty, right_meta.ty)) {
            EM_error(a->pos, "same type required");
            return expTy(NULL, Ty_Int());
        } 
        if (Ty_isString(left_meta.ty)) {
            return expTy(Tr_stringCompare(oper, left_meta.exp, right_meta.exp), Ty_Int());
        }
    }

    Tr_exp tr_exp = Tr_opExp(oper, left_meta.exp, right_meta.exp);
    return expTy(tr_exp, Ty_Int());
}

expty transRecordExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    S_symbol ty_name = a->u.record.typ;
    Ty_ty ty_original = S_checkedLookTy(tenv, ty_name, a->pos);
    Ty_ty ty;
    Tr_expList tr_expList = Tr_ExpList(NULL, NULL);
    Tr_expList tr_expListTail = tr_expList;

    if (!ty_original) {
        return expTy(NULL, Ty_Record(NULL));
    }
    ty = actual_ty(ty_original);

    if (!ty) {
        return expTy(NULL, Ty_Record(NULL));
    }

    if (ty->kind != Ty_record) {
        EM_error(a->pos, "invalid record type");
        return expTy(NULL, Ty_Record(NULL));
    }

    Ty_fieldList ty_fields = ty->u.record;
    A_efieldList efields = a->u.record.fields;
    int nfields = 0;
    // check types of fields
    do {
        Ty_field ty_field = ty_fields->head;
        A_efield efield = efields->head;

        if (ty_field->name != efield->name) {
            EM_error(a->pos, "field %s doesn't exist", S_name(efield->name));
            return expTy(NULL, Ty_Record(NULL));
        }

        expty exp_meta = transExp(venv, tenv, level, efield->exp);
        if (!Ty_isCompatible(ty_field->ty, exp_meta.ty)) {
            EM_error(a->pos, "incompatible field type");
            return expTy(NULL, Ty_Record(NULL));
        }
        tr_expListTail = tr_expListTail->tail = Tr_ExpList(exp_meta.exp, NULL);
        ++nfields;
        ty_fields = ty_fields->tail;
        efields = efields->tail;
    } while (ty_fields && efields);
    
    if (ty_fields || efields) {
        EM_error(a->pos, "inconsistent number of fields");
        return expTy(NULL, Ty_Record(NULL));
    }
    
    tr_expList = tr_expList->tail;
    Tr_exp tr_exp = Tr_recordExp(tr_expList);
    return expTy(tr_exp, ty_original);
}

expty transSeqExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    A_expList exps = a->u.seq;

    if (!exps) {
        return expTy(Tr_Nop(), Ty_Void());
    }
    expty seqResult;
    Tr_expList tr_expList = Tr_ExpList(NULL, NULL);
    Tr_expList tr_expListTail = tr_expList;
    do {
        A_exp exp = exps->head;
        expty result = transExp(venv, tenv, level, exp);
        tr_expListTail = tr_expListTail->tail = Tr_ExpList(result.exp, NULL);
        seqResult.ty = result.ty;
    } while ((exps = exps->tail));

    bool hasReturnValue = !Ty_isVoid(seqResult.ty);
    seqResult.exp = Tr_seqExp(tr_expList->tail, hasReturnValue);

    return seqResult;
}

expty transAssignExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    if (a->u.assign.var->kind == A_simpleVar) {
        E_enventry entry = S_look(venv, a->u.assign.var->u.simple);
        if (entry && entry->readonly) {
            EM_error(a->pos, "loop variable can't be assigned");
        }
    }

    expty var_meta = transVar(venv, tenv, level, a->u.assign.var),
          exp_meta = transExp(venv, tenv, level, a->u.assign.exp);
    if (!Ty_isSame(var_meta.ty, exp_meta.ty)) {
        EM_error(a->pos, "unmatched assign exp");
    }

    Tr_exp tr_exp = Tr_assignExp(var_meta.exp, exp_meta.exp);
    return expTy(tr_exp, Ty_Void());
}

expty transIfExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    expty cond_meta = transExp(venv, tenv, level, a->u.iff.test), 
          then_meta = transExp(venv, tenv, level, a->u.iff.then); 
    Tr_exp tr_else = NULL;

    if (a->u.iff.elsee) {
        expty else_meta = transExp(venv, tenv, level, a->u.iff.elsee);
        tr_else = else_meta.exp;
        if (!Ty_isCompatible(then_meta.ty, else_meta.ty)) {
            EM_error(a->pos, "then exp and else exp type mismatch");
        }
    } else if (!Ty_isVoid(then_meta.ty)) {
        EM_error(a->pos, "if-then exp's body must produce no value");
    }
    
    Tr_exp tr_exp = Tr_ifExp(cond_meta.exp, then_meta.exp, tr_else);
    return expTy(tr_exp, then_meta.ty);
}

expty transWhileExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
   expty cond_meta = transExp(venv, tenv, level, a->u.whilee.test);
   Temp_label done = startLoop();
   expty body_meta= transExp(venv, tenv, level, a->u.whilee.body);

   if (body_meta.ty->kind != Ty_void) {
       EM_error(a->pos, "while body must produce no value");
   }

   Tr_exp tr_exp = Tr_whileExp(cond_meta.exp, body_meta.exp, done);
   endLoop();

   return expTy(tr_exp, Ty_Void());
}

expty transForExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    S_beginScope(venv);
    expty lo_meta = transExp(venv, tenv, level, a->u.forr.lo),
          hi_meta = transExp(venv, tenv, level, a->u.forr.hi);
    
    if(!Ty_isInt(lo_meta.ty) || !Ty_isInt(hi_meta.ty)) {
        EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
    }

    Temp_label done = startLoop();
    Tr_access access = Tr_allocLocal(level, a->u.forr.escape);
    S_enter(venv, a->u.forr.var, E_ROVarEntry(access, Ty_Int()));
    
    expty body_meta = transExp(venv, tenv, level, a->u.forr.body);

    Tr_exp tr_exp = Tr_forExp(Tr_simpleVar(access, level), lo_meta.exp, hi_meta.exp, body_meta.exp, done);

    endLoop();
    S_endScope(venv);

    return expTy(tr_exp, Ty_Void());
}

expty transBreakExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    Temp_label done = currentLoop();
    if (!done) {
        EM_error(a->pos, "break outside loop");
        return expTy(Tr_Nop(), Ty_Void()); 
    }
    return expTy(Tr_breakExp(done), Ty_Void());
}

expty transLetExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    A_decList decs = a->u.let.decs;
    Tr_expList tr_decs = Tr_ExpList(NULL, NULL), tr_decs_cur = tr_decs;

    do {
        A_dec dec = decs->head;
        tr_decs_cur = tr_decs_cur->tail = Tr_ExpList(transDec(venv, tenv, level, dec), NULL);

    } while ((decs = decs->tail));

    tr_decs = tr_decs->tail;

    S_beginScope(venv);
    S_beginScope(tenv);

    expty result = transExp(venv, tenv, level, a->u.let.body);
    result.exp = Tr_letExp(tr_decs, result.exp);

    S_endScope(venv);
    S_endScope(tenv);
    
    return result;
}

expty transArrayExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    Ty_ty ty_array = S_checkedLookTy(tenv, a->u.array.typ, a->pos);
    
    if (!ty_array) {
        return expTy(Tr_Nop(), Ty_Array(NULL));
    }

    Ty_ty ty_actual_array = actual_ty(ty_array);
    Ty_ty ty_elmt = ty_actual_array->u.array;

    expty size_meta = transExp(venv, tenv, level, a->u.array.size), 
          init_meta = transExp(venv, tenv, level, a->u.array.init);

    if (!Ty_isInt(size_meta.ty)) {
        EM_error(a->u.array.size->pos, "array size type should be int");
    }
    if (!Ty_isCompatible(init_meta.ty, ty_elmt)) {
        EM_error(a->u.array.init->pos, "type mismatch");
    }

    Tr_exp tr_exp = Tr_arrayExp(size_meta.exp, init_meta.exp);
    return expTy(tr_exp, ty_array);
}

expty transExp(S_table venv, S_table tenv, Tr_level level, A_exp a) {
    switch (a->kind) {
    case A_varExp: 
        return transVar(venv, tenv, level, a->u.var);
    case A_nilExp:
        return transNilExp(venv, tenv, level, a);
    case A_intExp:
        return transIntExp(venv, tenv, level, a);
    case A_stringExp:
        return transStringExp(venv, tenv, level, a);
    case A_callExp:
        return transCallExp(venv, tenv, level, a);
    case A_opExp:
        return transOpExp(venv, tenv, level, a);
    case A_recordExp:
        return transRecordExp(venv, tenv, level, a);
    case A_seqExp:
        return transSeqExp(venv, tenv, level, a);
    case A_assignExp:
        return transAssignExp(venv, tenv, level, a);
    case A_ifExp:
        return transIfExp(venv, tenv, level, a);
    case A_whileExp:
        return transWhileExp(venv, tenv, level, a);
    case A_forExp:
        return transForExp(venv, tenv, level, a);
    case A_breakExp:
        return transBreakExp(venv, tenv, level, a);
    case A_letExp:
        return transLetExp(venv, tenv, level, a);
    case A_arrayExp:
        return transArrayExp(venv, tenv, level, a);
    default: break; // unreachable
    }
}

Tr_exp transVarDec(S_table venv, S_table tenv, Tr_level level, A_dec d) {
    expty init_meta = transExp(venv,tenv, level, d->u.var.init);
    Ty_ty ty_actual = init_meta.ty;
    S_symbol expected_type_name = d->u.var.typ;

    if (!S_isEmpty(expected_type_name)) {
        Ty_ty ty_expected = S_checkedLookTy(tenv, expected_type_name, d->pos);
        if (!ty_expected) {
            return NULL;
        }
    
        if (!Ty_isCompatible(ty_actual, ty_expected)) {
            EM_error(d->pos, "type mismatch");
            return NULL;
        }
    } else if (Ty_isSame(ty_actual, Ty_Nil())) {
        EM_error(d->pos, "init should not be nil without type specified");
        return NULL;
    }

    Tr_access tr_access = Tr_allocLocal(level, d->u.var.escape); 
    S_enter(venv, d->u.var.var, E_VarEntry(tr_access, ty_actual));
    
    Tr_exp tr_exp = Tr_assignExp(Tr_simpleVar(tr_access, level), init_meta.exp);

    return tr_exp;
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList fields) {
    // fields == NULL if takes no params
    if (!fields) return NULL;

    Ty_tyList tys = Ty_TyList(NULL, NULL), tail = tys;
    do {
        A_field field = fields->head;
        Ty_ty ty = S_look(tenv, field->typ);
        if (!ty) {
            EM_error(field->pos, "unknown param type");
        }
        
        tail = tail->tail = Ty_TyList(ty, NULL);
        
    } while ((fields = fields->tail));

    Ty_tyList old = tys;
    tys = tys->tail;
    free(old);

    return tys;
}

U_boolList makeFormalEscapeList(A_fieldList fields) {
    if (!fields) return NULL;
    U_boolList escapes = U_BoolList(FALSE, NULL), tail = escapes;

    do {
        A_field field = fields->head;
        tail = tail->tail = U_BoolList(TRUE, NULL);
    } while ((fields = fields->tail));

    U_boolList old = escapes;
    escapes = escapes->tail;
    free(old);

    return escapes;
}

void transFunctionDec(S_table venv, S_table tenv, Tr_level level, A_dec d) {
    A_fundecList funcs = d->u.function;
    
    // first loop
    do {
        A_fundec f = funcs->head;
        Ty_ty ty_result;
        if (S_isEmpty(f->result)) 
            ty_result = Ty_Void();
        else {
            ty_result = S_checkedLookTy(tenv,f->result, f->pos);
        }

        Ty_tyList ty_formals = makeFormalTyList(tenv,f->params);

        if (!isUniqueFuncName(funcs, f)) {
            EM_error(f->pos, "two functions have the same name");
            continue;
        }
        // Temp_label label = Temp_namedlabel(S_name(f->name));
        Temp_label label = Temp_newlabel();
        Tr_level func_level = Tr_newLevel(level, label, makeFormalEscapeList(f->params) ); 
        S_enter(venv,f->name,E_FunEntry(func_level, label, ty_formals, ty_result));
    } while ((funcs = funcs->tail));

    // second loop
    funcs = d->u.function;
    do {   
        A_fundec f = funcs->head;

        E_enventry ty_entry = S_look(venv, f->name);
        Ty_tyList ty_formals = ty_entry->u.fun.formals;
        Ty_ty ty_result = ty_entry->u.fun.result;

        S_beginScope(venv);
        S_beginScope(tenv);

        A_fieldList l; 
        Ty_tyList t;
        Tr_level func_level = ty_entry->u.fun.level;
        Tr_accessList tr_formals = Tr_formals(func_level);
        Tr_accessList acc = tr_formals;
        for(    l=f->params, t=ty_formals;
                l; 
                l=l->tail, t=t->tail, acc = acc->tail) {
            S_enter(venv,l->head->name, E_VarEntry(acc->head, t->head));
        }
        expty body_meta = transExp(venv, tenv, func_level, f->body);
        
        if (Ty_isVoid(ty_result) && !Ty_isVoid(body_meta.ty)) {
            EM_error(f->body->pos, "procedure returns value");
        } else if (!Ty_isCompatible(ty_result, body_meta.ty)) {
            EM_error(f->body->pos, "inconsistent return type");
        }

        Tr_procEntryExit(func_level, body_meta.exp, tr_formals, Ty_isVoid(body_meta.ty));

        S_endScope(tenv);
        S_endScope(venv);
    } while ((funcs = funcs->tail));
}

void transTypeDec(S_table venv, S_table tenv, Tr_level level, A_dec d) {
    A_nametyList types = d->u.type;
    A_nametyList cur = types;
    
    // first loop: put names
    do {
        A_namety head = cur->head;
        S_symbol name = head->name;

        if (!isUniqueTyName(types, head)) {
            EM_error(d->pos, "two types have the same name");
            continue;
        }
        S_enter(tenv, name, Ty_Name(name, NULL));
    } while ((cur = cur->tail));

    // second loop: put bindings
    cur = types;
    do {
        A_namety head = cur->head;
        Ty_ty ty = S_checkedLookTy(tenv, head->name, d->pos);
        if (!ty) continue;

        Ty_ty actual = transTy(tenv, head->ty);
        ty->u.name.ty = actual;

        // detect cycles
        if (Ty_hasCycle(ty)) {
            EM_error(d->pos, "illegal type cycle");
        }
    } while ((cur = cur->tail));
}

Tr_exp transDec(S_table venv, S_table tenv, Tr_level level, A_dec d) {
    switch (d->kind) {
        case A_varDec:
            return transVarDec(venv, tenv, level, d);
        case A_functionDec:
            transFunctionDec(venv, tenv, level, d);
            return Tr_Nop();
        case A_typeDec:
            transTypeDec(venv, tenv, level, d);
            return Tr_Nop();
        default: break; // unreachable
    }
}

Ty_ty transNameTy(S_table tenv, A_ty a) {
    S_symbol name = a->u.name;
    Ty_ty ty = S_checkedLookTy(tenv, name, a->pos);

    return Ty_Name(name, ty);
}


Ty_ty transRecordTy(S_table tenv, A_ty a) {
    A_fieldList fields = a->u.record;
    Ty_fieldList ty_fields = Ty_FieldList(NULL, NULL); // fake head node
    Ty_fieldList ty_tail = ty_fields; // last node (not null)

    do {
        A_field cur = fields->head;
        S_symbol ty_name = cur->typ;
        Ty_ty ty = S_checkedLookTy(tenv, ty_name, cur->pos);
        if (!ty) {
            return Ty_Record(NULL);
        }
        Ty_field ty_field = Ty_Field(cur->name, ty);
        ty_tail->tail = Ty_FieldList(ty_field, NULL);
        ty_tail = ty_tail->tail;
    } while ((fields = fields->tail));
    // remove fake head
    Ty_fieldList old = ty_fields;
    ty_fields = ty_fields->tail;
    free(old);

    return Ty_Record(ty_fields);
}

Ty_ty transArrayTy(S_table tenv, A_ty a) {
    S_symbol name = a->u.array;
    Ty_ty ty_elmt = S_look(tenv, name);
    if (!ty_elmt) {
        EM_error(a->pos, "");
        return NULL;
    }
    return Ty_Array(ty_elmt);
}


Ty_ty transTy(S_table tenv, A_ty a) {
    switch (a->kind) {
    case A_nameTy: 
        return transNameTy(tenv, a);
    case A_recordTy: 
        return transRecordTy(tenv, a);
    case A_arrayTy: 
        return transArrayTy(tenv, a);
    default: break; // unreachable
    }
}


F_fragList SEM_transProg (A_exp exp) {
    loopStack = Stack_Init();

    S_table root_tenv = E_base_tenv(), root_venv = E_base_venv();
    
    Tr_exp body = transExp(root_venv, root_tenv, Tr_outermost(), exp).exp;
    Tr_procEntryExit(Tr_outermost(), body, NULL, TRUE);
    
    Stack_Destroy(loopStack);
    return Tr_getResult();
}

