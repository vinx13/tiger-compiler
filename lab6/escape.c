#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "escape.h"
#include "table.h"

typedef struct escapeEntry_ {
    int depth;
    bool *esc;
} *escapeEntry;

static escapeEntry EscapeEntry(int d, bool *esc) {
    escapeEntry p = (escapeEntry)checked_malloc(sizeof(*p));
    p->depth = d;
    p->esc = esc;
    return p;
}

static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env, int depth, A_var v);
static void traverseExp(S_table env, int depth, A_exp e) {
    switch (e->kind) {
    case A_varExp:
        traverseVar(env, depth, e->u.var); break;
    case A_letExp: {
        S_beginScope(env);
        A_decList decs = e->u.let.decs;
        for(; decs; decs = decs->tail) {
            traverseDec(env, depth, decs->head);
        }
        traverseExp(env, depth, e->u.let.body);
        S_endScope(env);
        break;
     }
    case A_callExp: {
        A_expList args = e->u.call.args;
        for (; args; args = args->tail) {
            traverseExp(env, depth, args->head);
        }
        break;
    }
    case A_opExp: {
        traverseExp(env, depth, e->u.op.left);
        traverseExp(env, depth, e->u.op.right);
        break;
    }
    case A_recordExp: {
        A_efieldList fields = e->u.record.fields;
        for (; fields; fields = fields->tail) {
            traverseExp(env, depth, fields->head->exp);
        }
        break;
    }
    case A_seqExp: {
        A_expList exps = e->u.seq;
        for (; exps; exps = exps->tail) {
            traverseExp(env, depth, exps->head);
        }
        break;
    }
    case A_assignExp: {
        traverseExp(env, depth, e->u.assign.exp);
        traverseVar(env, depth, e->u.assign.var);
        break;
    }
    case A_ifExp: {
        traverseExp(env, depth, e->u.iff.test);
        traverseExp(env, depth, e->u.iff.then);
        if (e->u.iff.elsee) {
            traverseExp(env, depth, e->u.iff.elsee);
        }
        break;
    }
    case A_whileExp: {
        traverseExp(env, depth, e->u.whilee.test);
        traverseExp(env, depth, e->u.whilee.body);
        break;
    }
    case A_forExp: {
         traverseExp(env, depth, e->u.forr.lo);
         traverseExp(env, depth, e->u.forr.hi);
         S_beginScope(env);
         S_enter(env, e->u.forr.var, EscapeEntry(depth, &e->u.forr.escape));
         traverseExp(env, depth, e->u.forr.body);
         S_endScope(env);
         break;
    }
    case A_arrayExp: {
        traverseExp(env, depth, e->u.array.size);
        traverseExp(env, depth, e->u.array.init);
        break;
    }
    default: break;
    }
}

static void traverseDec(S_table env, int depth, A_dec d) {
    switch (d->kind) {
    case A_varDec: {
        traverseExp(env, depth, d->u.var.init);
        S_enter(env, d->u.var.var, EscapeEntry(depth, &d->u.var.escape));
        break;
    }
    case A_functionDec: {
        A_fundecList funs = d->u.function;
        for (; funs; funs = funs->tail) {
            S_beginScope(env);
            A_fieldList fields = funs->head->params;
            for (; fields; fields = fields->tail) {
                A_field f = fields->head;
                S_enter(env, f->name, EscapeEntry(depth + 1, &f->escape));
            }
            traverseExp(env, depth + 1, funs->head->body);
            S_endScope(env);
        }
        break;
    }
    default:
        break;
    }
}

static void traverseVar(S_table env, int depth, A_var v) {
    switch (v->kind) {
    case A_simpleVar: {
        escapeEntry entry = S_look(env, v->u.simple);
        if (!entry) {
            printf("%s\n", S_name(v->u.simple));
            assert(entry);
        }
        if (entry->depth != depth) {
            printf("%s escape\n", S_name(v->u.simple));
            *(entry->esc) = TRUE;
        }
        break;
    }
    case A_fieldVar: {
        traverseVar(env, depth, v->u.field.var);
        break;
    }
    case A_subscriptVar: {
        traverseVar(env, depth, v->u.subscript.var);
        traverseExp(env, depth, v->u.subscript.exp);
        break;
    }
    }
}

void Esc_findEscape(A_exp exp) {
	//your code here	
    traverseExp(S_empty(), 0, exp);
}
