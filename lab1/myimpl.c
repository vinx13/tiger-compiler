#include "prog1.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static int maxArg = 0, printEnabled = 0;

typedef struct TableTag {
    string id; 
    int value; 
    struct TableTag *tail;
} *Table_;

Table_ Table(string id, int value, Table_ tail) {
    Table_ t = malloc(sizeof(*t)); t->id=id; t->value=value; t->tail=tail; return t;
}

typedef struct {
    int i; 
    Table_ t;
} IntAndTable;

Table_ interpStm(A_stm s, Table_ t);

int lookup(Table_ t, string key) {
    do {
        if (~strcmp(t->id, key)) 
            return t->value;
        t = t->tail;
    } while (t);
}

int evalBinaryOp(int left, A_binop op, int right) {
    switch (op) {
        case A_plus:
            return left + right;
        case A_minus:
            return left - right;
        case A_times:
            return left * right;
        case A_div:
            return left / right;
    }
}

IntAndTable interpExp(A_exp e, Table_ t) {
    IntAndTable result;
    result.t = t;

    switch (e->kind) {
        case A_idExp: {
            result.i = lookup(t, e->u.id);
            break;
        }
        case A_numExp: {
            result.i = e->u.num;
            break;
        }
        case A_opExp: {
            IntAndTable left = interpExp(e->u.op.left, t), right = interpExp(e->u.op.right, t);
            result.i = evalBinaryOp(left.i, e->u.op.oper, right.i);
            break;
        }
        case A_eseqExp: {
            return interpExp(e->u.eseq.exp, interpStm(e->u.eseq.stm, t));
        }
    }

    return result;
}

void printExps(A_expList exps, Table_ t, int argCount) {
    if (argCount > maxArg) {
        maxArg = argCount;
    }

    switch (exps->kind) {
        case A_pairExpList: {
            IntAndTable result = interpExp(exps->u.pair.head, t);
            if (printEnabled) printf("%d ", result.i);
            printExps(exps->u.pair.tail, t, argCount + 1);
            break;
        }
        case A_lastExpList: {
            IntAndTable result = interpExp(exps->u.last, t);
            if (printEnabled) printf("%d\n", result.i);
            break;
        }
    }
}

Table_ interpStm(A_stm s, Table_ t) {
    switch (s->kind) {
        case A_compoundStm:
            return interpStm(s->u.compound.stm2, 
                    interpStm(s->u.compound.stm1, t));
        case A_assignStm: {
            IntAndTable result = interpExp(s->u.assign.exp, t);
            return Table(s->u.assign.id, result.i, result.t);
        }
        case A_printStm: {
            printExps(s->u.print.exps, t, 1);
            return t;
        }
    }
}



int maxargs(A_stm stm) {
    printEnabled = 0;
    maxArg = 0;
    interpStm(stm, NULL);
    return maxArg;
}


void interp(A_stm stm) {
    printEnabled = 1;
    maxArg = 0;
    interpStm(stm, NULL);
}

