#include <stdio.h>
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

/*Lab4: Your implementation of lab4*/

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
    for (Ty_ty cur = ty->u.name.ty; cur->kind == Ty_name && cur->u.name.ty /* named type may be incomplete */; cur = cur->u.name.ty) {
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

int S_isEmpty(S_symbol s) {
    return !s || s == S_Symbol("");
}

int Ty_isSame(Ty_ty ty1, Ty_ty ty2) {
    return actual_ty(ty1) == actual_ty(ty2);
    Ty_ty actual1 = actual_ty(ty1), actual2 = actual_ty(ty2);
    if (actual1 == actual2) return TRUE;
    if (actual1->kind != actual2->kind) return FALSE;

    // no need to check record or array type
    return TRUE;
}

int Ty_isInt(Ty_ty ty) {
    return Ty_isSame(ty, Ty_Int());
}

int Ty_isVoid(Ty_ty ty) {
    return Ty_isSame(ty, Ty_Void());
}

expty transSimpleVar(S_table venv, S_table tenv, A_var v) {
    E_enventry x = S_look(venv,v->u.simple);
    if (x && x->kind==E_varEntry)
        return expTy(NULL, actual_ty(x->u.var.ty));
    else {
        EM_error(v->pos,"undefined variable %s", S_name(v->u.simple));
        return expTy(NULL,Ty_Int());
    }
}

expty transFieldVar(S_table venv, S_table tenv, A_var v) {
    A_var rec = v->u.field.var;
    S_symbol field_name = v->u.field.sym;

    expty rec_meta = transVar(venv, tenv, rec);
    Ty_ty ty_rec = actual_ty(rec_meta.ty);

    if (ty_rec->kind != Ty_record) {
        EM_error(v->pos, "not a record type");
        return expTy(NULL, Ty_Int());
    }
    Ty_fieldList fields = ty_rec->u.record;
    
    // search through field list
    Ty_field field = NULL;
    while (fields) {
        if (fields->head->name == field_name) 
            field = fields->head;
        fields = fields->tail;
    }
    if (!field) { // not found
        EM_error(v->pos, "field %s doesn't exist", S_name(field_name));
        return expTy(NULL, Ty_Int());
    }

    return expTy(NULL, actual_ty(field->ty));
}

expty transSubscriptVar(S_table venv, S_table tenv, A_var v) {
    A_var arr = v->u.subscript.var;
    A_exp idx = v->u.subscript.exp;
    expty arr_meta = transVar(venv, tenv, arr);
    expty idx_meta = transExp(venv, tenv, idx);
    
    // check arr
    if (arr_meta.ty->kind != Ty_array) {
        EM_error(v->pos, "array type required");
        return expTy(NULL, Ty_Int());
    }
    // check idx
    if (!(idx_meta.ty->kind != Ty_int)) {
        EM_error(v->pos, "");
        return expTy(NULL, Ty_Int());
    }

    return expTy(NULL, actual_ty(arr_meta.ty->u.array));
}

expty transVar(S_table venv, S_table tenv, A_var v) {
    switch(v->kind) {
    case A_simpleVar: 
        return transSimpleVar(venv, tenv, v);
    case A_fieldVar: 
        return transFieldVar(venv, tenv, v);
    case A_subscriptVar:
        return transSubscriptVar(venv, tenv, v);
    default: break; // unreachable
    }
}

expty transNilExp(S_table venv, S_table tenv, A_exp a) {
    return expTy(NULL, Ty_Nil());
}

expty transIntExp(S_table venv, S_table tenv, A_exp a) {
    return expTy(NULL, Ty_Int());
}

expty transStringExp(S_table venv, S_table tenv, A_exp a) {
    return expTy(NULL, Ty_String());
}

expty transCallExp(S_table venv, S_table tenv, A_exp a) {
    S_symbol func_name = a->u.call.func;
    E_enventry func_entry = S_checkedLookFunc(venv, func_name, a->pos);

    if (!func_entry) {
        return expTy(NULL, Ty_Void());
    }
    
    A_expList args = a->u.call.args;
    Ty_tyList ty_formals = func_entry->u.fun.formals;
    
    
    while (ty_formals && args) { 
        A_exp arg = args->head;
        Ty_ty ty_formal = ty_formals->head;
        expty arg_meta = transExp(venv, tenv, arg);
        if (!Ty_isSame(ty_formal, arg_meta.ty)) {
            EM_error(arg->pos, "para type mismatch");
        }
        ty_formals = ty_formals->tail;
        args = args->tail;
    }
        
    if (args || ty_formals) {
            EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
    }

    return expTy(NULL, func_entry->u.fun.result);
}

expty transOpExp(S_table venv, S_table tenv, A_exp a) {
    A_oper oper = a->u.op.oper;
    expty left_meta = transExp(venv, tenv, a->u.op.left);
    expty right_meta = transExp(venv, tenv, a->u.op.right);

    if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
        if (left_meta.ty->kind != Ty_int) {
            EM_error(a->u.op.left->pos, "integer required");
        }
        if (right_meta.ty->kind != Ty_int) {
            EM_error(a->u.op.right->pos,"integer required");
        }
    } else { // cmp ops
        if (!Ty_isSame(left_meta.ty, right_meta.ty)) {
            EM_error(a->pos, "same type required");
            return expTy(NULL, Ty_Int());
        }
    }
    return expTy(NULL, Ty_Int());
}

expty transRecordExp(S_table venv, S_table tenv, A_exp a) {
    S_symbol ty_name = a->u.record.typ;
    Ty_ty ty_original = S_checkedLookTy(tenv, ty_name, a->pos), ty;

    if (!ty_original) {
        return expTy(NULL, Ty_Record(NULL));
    }
    ty = actual_ty(ty_original);

    if (!ty) {
        return expTy(NULL, Ty_Record(NULL));
    }
    if (ty->kind != Ty_record) {
        EM_error(a->pos, "");
        return expTy(NULL, Ty_Record(NULL));
    }

    Ty_fieldList ty_fields = ty->u.record;
    A_efieldList efields = a->u.record.fields;

    // check types of fields
    do {
        Ty_field ty_field = ty_fields->head;
        A_efield efield = efields->head;

        if (ty_field->name != efield->name) {
            EM_error(a->pos, "field %s doesn't exist", S_name(efield->name));
            return expTy(NULL, Ty_Record(NULL));
        }

        expty exp_meta = transExp(venv, tenv, efield->exp);
        if (!Ty_isSame(ty_field->ty, exp_meta.ty)) {
            EM_error(a->pos, "");
            return expTy(NULL, Ty_Record(NULL));
        }
        ty_fields = ty_fields->tail;
        efields = efields->tail;
    } while (ty_fields && efields);
    
    if (ty_fields || efields) {
        // the number of fields does not match
        EM_error(a->pos, "");
        
        return expTy(NULL, Ty_Record(NULL));
    }
    
    return expTy(NULL, ty_original);
}

expty transSeqExp(S_table venv, S_table tenv, A_exp a) {
    A_expList exps = a->u.seq;

    if (!exps) {
        return expTy(NULL, Ty_Void());
    }
    expty result;
    do {
        A_exp exp = exps->head;
        result = transExp(venv, tenv, exp);
    } while ((exps = exps->tail));

    return result;
}

expty transAssignExp(S_table venv, S_table tenv, A_exp a) {
    if (a->u.assign.var->kind == A_simpleVar) {
        E_enventry entry = S_look(venv, a->u.assign.var->u.simple);
        if (entry && entry->readonly) {
            EM_error(a->pos, "loop variable can't be assigned");
        }
    }

    expty var_meta = transVar(venv, tenv, a->u.assign.var),
          exp_meta = transExp(venv, tenv, a->u.assign.exp);
    if (!Ty_isSame(var_meta.ty, exp_meta.ty)) {
        EM_error(a->pos, "unmarched assign exp");
    }

    return expTy(NULL, var_meta.ty);
}

expty transIfExp(S_table venv, S_table tenv, A_exp a) {
    expty cond_meta = transExp(venv, tenv, a->u.iff.test), 
          then_meta = transExp(venv, tenv, a->u.iff.then); 

    if (a->u.iff.elsee) {
        expty else_meta = transExp(venv, tenv, a->u.iff.elsee);
        if (!Ty_isSame(then_meta.ty, else_meta.ty)) {
            EM_error(a->pos, "then exp and else exp type mismatch");
        }
    } else if (!Ty_isVoid(then_meta.ty)) {
        EM_error(a->pos, "if-then exp's body must produce no value");
    }
    
    return expTy(NULL, then_meta.ty);
}

expty transWhileExp(S_table venv, S_table tenv, A_exp a) {
   expty cond_meta = transExp(venv, tenv, a->u.whilee.test), 
         body_meta= transExp(venv, tenv, a->u.whilee.body);

   if (body_meta.ty->kind != Ty_void) {
       EM_error(a->pos, "while body must produce no value");
   }
   return expTy(NULL, Ty_Void());
}

expty transForExp(S_table venv, S_table tenv, A_exp a) {
    S_beginScope(venv);
    expty lo_meta = transExp(venv, tenv, a->u.forr.lo),
          hi_meta = transExp(venv, tenv, a->u.forr.hi);
    
    if(!Ty_isInt(lo_meta.ty) || !Ty_isInt(hi_meta.ty)) {
        EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
    }

    S_enter(venv, a->u.forr.var, E_ROVarEntry(Ty_Int()));
    
    expty body_meta = transExp(venv, tenv, a->u.forr.body);

    S_endScope(venv);

    return expTy(NULL, Ty_Void());
}

expty transBreakExp(S_table venv, S_table tenv, A_exp a) {
    return expTy(NULL, Ty_Void());
}

expty transLetExp(S_table venv, S_table tenv, A_exp a) {
    A_decList decs = a->u.let.decs;

    do {
        A_dec dec = decs->head;
        transDec(venv, tenv, dec); 
    } while ((decs = decs->tail));

    return transExp(venv, tenv, a->u.let.body);
}

expty transArrayExp(S_table venv, S_table tenv, A_exp a) {
    Ty_ty ty_elmt = S_checkedLookTy(tenv, a->u.array.typ, a->pos);

    if (!ty_elmt) {
        return expTy(NULL, Ty_Array(NULL));
    }

    expty size_meta = transExp(venv, tenv, a->u.array.size), 
          init_meta = transExp(venv, tenv, a->u.array.init);

    if (!Ty_isInt(size_meta.ty)) {
        EM_error(a->u.array.size->pos, "");
    }
    if (!Ty_isInt(init_meta.ty)) {
        EM_error(a->u.array.init->pos, "type mismatch");
    }

    return expTy(NULL, Ty_Array(ty_elmt));
}

expty transExp(S_table venv, S_table tenv, A_exp a) {
    switch (a->kind) {
    case A_varExp: 
        return transVar(venv, tenv, a->u.var);
    case A_nilExp:
        return transNilExp(venv, tenv, a);
    case A_intExp:
        return transIntExp(venv, tenv, a);
    case A_stringExp:
        return transStringExp(venv, tenv, a);
    case A_callExp:
        return transCallExp(venv, tenv, a);
    case A_opExp:
        return transOpExp(venv, tenv, a);
    case A_recordExp:
        return transRecordExp(venv, tenv, a);
    case A_seqExp:
        return transSeqExp(venv, tenv, a);
    case A_assignExp:
        return transAssignExp(venv, tenv, a);
    case A_ifExp:
        return transIfExp(venv, tenv, a);
    case A_whileExp:
        return transWhileExp(venv, tenv, a);
    case A_forExp:
        return transForExp(venv, tenv, a);
    case A_breakExp:
        return transBreakExp(venv, tenv, a);
    case A_letExp:
        return transLetExp(venv, tenv, a);
    case A_arrayExp:
        return transArrayExp(venv, tenv, a);
    default: break; // unreachable
    }
}

void transVarDec(S_table venv, S_table tenv, A_dec d) {
    expty init_meta = transExp(venv,tenv,d->u.var.init);
    Ty_ty ty_actual = init_meta.ty;
    S_symbol expected_type_name = d->u.var.typ;

    if (!S_isEmpty(expected_type_name)) {
        Ty_ty ty_expected = S_checkedLookTy(tenv, expected_type_name, d->pos);
        if (!ty_expected) {
            return;
        }
    
        if (!Ty_isSame(ty_actual, ty_expected)) {
            EM_error(d->pos, "type mismatch");
            return;
        }
    } else if (Ty_isSame(ty_actual, Ty_Nil())) {
        EM_error(d->pos, "init should not be nil without type specified");
        return;
    }

    S_enter(venv, d->u.var.var, E_VarEntry(ty_actual));
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList fields) {
    // fields == NULL if takes no params
    if (!fields) return NULL;

    Ty_tyList tys = Ty_TyList(NULL, NULL), cur = tys;
    do {
        A_field field = fields->head;
        Ty_ty ty = S_look(tenv, field->typ);
        if (!ty) {
            EM_error(field->pos, "");
        }
        
        cur->tail = Ty_TyList(ty, NULL);
        cur = cur->tail;
    } while ((fields = fields->tail));

    Ty_tyList old = tys;
    tys = tys->tail;
    free(old);

    return tys;
}

void transFunctionDec(S_table venv, S_table tenv, A_dec d) {
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

        if (S_look(venv, f->name)) {
            EM_error(f->pos, "two functions have the same name");
            continue;
        }
        S_enter(venv,f->name,E_FunEntry(ty_formals, ty_result));
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
        for(l=f->params, t=ty_formals; l; l=l->tail, t=t->tail) {
            S_enter(venv,l->head->name,E_VarEntry(t->head));
        }
        expty body_meta = transExp(venv, tenv, f->body);
        
        if (Ty_isVoid(ty_result) && !Ty_isVoid(body_meta.ty)) {
            EM_error(f->body->pos, "procedure returns value");
        } else if (!Ty_isSame(ty_result, body_meta.ty)) {
            EM_error(f->body->pos, "");
        }

        S_endScope(tenv);
        S_endScope(venv);
    } while ((funcs = funcs->tail));
}

void transTypeDec(S_table venv, S_table tenv, A_dec d) {
    A_nametyList types = d->u.type;
    A_nametyList cur = types;

    // first loop: put names
    do {
        A_namety head = cur->head;
        S_symbol name = head->name;

        if (S_look(tenv, name)) {
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

void transDec(S_table venv, S_table tenv, A_dec d) {
    switch (d->kind) {
        case A_varDec:
            transVarDec(venv, tenv, d);
            return;
        case A_functionDec:
            transFunctionDec(venv, tenv, d);
            return;
        case A_typeDec:
            transTypeDec(venv, tenv, d);
            return;
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

void loadBuiltins(S_table venv, S_table tenv) {
}

void SEM_transProg (A_exp exp) {
    S_table root_tenv = E_base_tenv(), root_venv = E_base_venv();
    
    loadBuiltins(root_venv, root_tenv);
    transExp(root_venv, root_tenv, exp);

    free(root_tenv);
    free(root_venv);
}

