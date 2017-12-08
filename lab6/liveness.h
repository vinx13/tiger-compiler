#ifndef LIVENESS_H
#define LIVENESS_H

#include "graph.h"

typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
    G_node src, dst;
    G_node flow;
    Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, G_node flow, Live_moveList tail);

G_table Live_liveness(G_graph flow);

#endif
