#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList AS_def(AS_instr instr) {
	if (instr->kind == I_OPER)
		return instr->u.OPER.dst;
	else if (instr->kind == I_MOVE) 
		return instr->u.OPER.dst;
	return NULL;
}

Temp_tempList FG_def(G_node n) {
	//your code here.
	AS_instr instr = (AS_instr)G_nodeInfo(n);
    return AS_def(instr);
}

Temp_tempList AS_use(AS_instr instr) {
	if (instr->kind == I_OPER)
		return instr->u.OPER.src;
	else if (instr->kind == I_MOVE)
		return instr->u.OPER.src;
	return NULL;
}

Temp_tempList FG_use(G_node n) {
	//your code here.
	AS_instr instr = (AS_instr)G_nodeInfo(n);
    return AS_use(instr);
}

bool FG_isMove(G_node n) {
	//your code here.
	AS_instr instr = G_nodeInfo(n);
	return instr->kind == I_MOVE;
	return TRUE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	//your code here.
	G_graph g = G_Graph();
	G_node prev = NULL;
	AS_instrList head = il;
	
	struct TAB_table_ *labelMap = TAB_empty();
	
	for (; il; il = il->tail) {
		AS_instr instr = il->head;
		G_node n = G_Node(g, (void *)instr);
		if (prev) {
			G_addEdge(prev, n);
		}
        if (instr->kind == I_OPER && 0 == strncmp("jmp", instr->u.OPER.assem, 3)) { 
            prev = NULL;
        } else {
            prev = n;
        }
		if (instr->kind == I_LABEL) {
			TAB_enter(labelMap, instr->u.LABEL.label, n);
		}
	}

    G_nodeList nodes = G_nodes(g);
	for (; nodes; nodes = nodes->tail) {
        G_node n = nodes->head;
        AS_instr instr = (AS_instr) G_nodeInfo(n);
		if (instr->kind == I_OPER && instr->u.OPER.jumps) {
			Temp_labelList labels = instr->u.OPER.jumps->labels;
			for (; labels; labels = labels->tail) {
				Temp_label label = labels->head;
				G_node dest = (G_node) TAB_look(labelMap, label);
				G_addEdge(n, dest);
			}
		}
	}
	return g;
}

