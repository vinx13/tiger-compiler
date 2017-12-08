#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"


Live_moveList Live_MoveList(G_node src, G_node dst, G_node flow, Live_moveList tail) {
    Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
    lm->src = src;
    lm->dst = dst;
    lm->flow = flow;
    lm->tail = tail;
    return lm;
}

static Temp_temp findInTempList(Temp_tempList l, Temp_temp e) {
    for (; l; l = l->tail) {
        if (l->head == e)
            return e;
    }
    return NULL;
}

G_table buildLiveMap(G_graph flow) {
    bool dirty;
    G_table livein = G_empty(), liveout = G_empty();
    G_nodeList rnodesHead = G_rnodes(flow), flownodes;
    do {
        dirty = FALSE;

        for (flownodes = rnodesHead; flownodes; flownodes = flownodes->tail) {
            G_node flownode = flownodes->head;
            printInstr(G_nodeInfo(flownode));
            Temp_tempList ins = G_look(livein, flownode),
                outs = G_look(liveout, flownode),
                uses = FG_use(flownode),
                defs = FG_def(flownode);

            for (; uses; uses = uses->tail) {
                if (!findInTempList(ins, uses->head)) {
                    ins = Temp_TempList(uses->head, ins);
                    dirty = TRUE;
                }
            }

            for (; outs; outs = outs->tail) {
                Temp_temp out = outs->head;
                if (!findInTempList(defs, out) && !findInTempList(ins, out)) {
                    ins = Temp_TempList(out, ins);
                    dirty = TRUE;
                }
            }

            outs = G_look(liveout, flownode);
            G_nodeList succs = G_succ(flownode);
            for (; succs; succs = succs->tail) {
                G_node succ = succs->head;
                Temp_tempList succIns = (Temp_tempList) G_look(livein, succ);
                for (; succIns; succIns = succIns->tail) {
                    Temp_temp succIn = succIns->head;
                    if (!findInTempList(outs, succIn)) {
                        outs = Temp_TempList(succIn, outs);
                        dirty = TRUE;
                    }
                }
            }
            G_enter(livein, flownode, (void *) ins);
            G_enter(liveout, flownode, (void *) outs);
        }
    } while (dirty);
    return liveout;
}

void printLiveMap(G_graph cfg, G_table liveMap) {
    printf("----------livemap---------------\n");
    G_nodeList nodes = G_nodes(cfg);
    for (; nodes; nodes = nodes->tail) {
        G_node n = nodes->head;
        printInstr(G_nodeInfo(n));
        Temp_tempList liveOuts = G_look(liveMap, n);
        for (; liveOuts; liveOuts = liveOuts->tail) {
            Temp_temp temp = liveOuts->head;
            printf("%s ", tempName(temp));
        }
        printf("\n");
    }
    printf("------------------------------\n");
}

G_table Live_liveness(G_graph flow) {
    //your code here.
    G_table liveMap = buildLiveMap(flow);

    printLiveMap(flow, liveMap);

    return liveMap;
}

