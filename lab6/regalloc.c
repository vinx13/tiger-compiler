#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"
#include "stack.h"

static G_graph flow, rig;
static Temp_tempList regs;
static G_nodeList simplifyWorklist, freezeWorklist, spillWorklist, spilledNodes, coalescedNodes, coloredNodes, selectStack;
static Live_moveList coalescedMoves, constrainedMoves, frozenMoves, worklistMoves, activeMoves;
static TAB_table worklistName;
static int adjSetDim;
static bool *adjSet;

static G_table adjList;
static G_table degree, alias, color, cost;
static G_table moveList;

static F_frame frame;
static AS_instrList instrList;

static G_table liveOut;
static Temp_map gtemp;
static Temp_tempList spilledTemps;


#define MAKE_FIND_IN_LIST(TYPE, NAME) \
static bool findIn##NAME##List(TYPE n, TYPE##List list) { \
    for(; list; list = list->tail) { \
        if (list->head == n) return TRUE; \
    } \
    return FALSE; \
}

MAKE_FIND_IN_LIST(G_node, Node)

MAKE_FIND_IN_LIST(Temp_temp, Temp)


static bool isPrecolored(G_node n) {
    Temp_temp t = G_nodeInfo(n);
    return findInTempList(t, regs);
}

static string nodeName(G_node n) {
    assert(n);
    Temp_temp t = G_nodeInfo(n);
    assert(t);
    string name = tempName(G_nodeInfo(n));
    assert(name);
    return name;
}


static string formatMove(Live_moveList m) {
    assert(m);
    char buf[256] = {0};
    sprintf(buf, "%s -> %s;", nodeName(m->src), nodeName(m->dst));
    return String(buf);
}

static void printMoveList(Live_moveList ms) {
    for (; ms; ms = ms->tail) {
        DEBUG_PRINT("%s ", formatMove(ms));
    }
}

static void printNodeList(G_nodeList ns) {
    if (!ns) {
        DEBUG_PRINT("(null)");
    }
    for (; ns; ns = ns->tail) {
        DEBUG_PRINT("%s; ", nodeName(ns->head));
    }
}

static int getDegree(G_node n) {
    return (int) G_look(degree, n);
}

static void setDegree(G_node n, int d) {
    assert(d >= 0);
    G_enter(degree, n, (void *) d);
}

static void printDegree(G_node n) {
    DEBUG_PRINT("Degree of %s: %d\n", nodeName(n), getDegree(n));
}

static Temp_temp getColor(G_node n) {
    if (isPrecolored(n)) {
        return (Temp_temp) G_nodeInfo(n);
    }
    return (Temp_temp) G_look(color, n);
}

static void setColor(G_node n, Temp_temp c) {
    G_enter(color, n, (void *) c);
}

static G_node getAlias(G_node n) {
    assert(n);
    if (findInNodeList(n, coalescedNodes)) {
        return getAlias((G_node) G_look(alias, n));
    }
    return n;
}

static void setAlias(G_node n, G_node a) {
    G_enter(alias, n, (void *) a);
}

static double getSpillCost(G_node n) {
    assert(n);
    double *p = (double *) G_look(cost, n);
    if (!p) {
        p = (double *) checked_malloc(sizeof(double));
        *p = 0.0;
        G_enter(cost, n, (void *) p);
    }
    assert (p);
    return *p;
}

static void setSpillCost(G_node n, double c) {
    assert(n && !isPrecolored(n));
    double *p = (double *) G_look(cost, n);
    *p = c;
}

static string getWorklistName(G_nodeList *p) {
    return (string) TAB_look(worklistName, p);
}

static void setWorklistName(G_nodeList *p, string n) {
    TAB_enter(worklistName, p, n);
}

static void nodeListEnter(G_node n, G_nodeList *pl) {
    assert(n);
    *pl = G_NodeList(n, *pl);
}

static void nodeListRemove(G_node n, G_nodeList *pl) {
    assert(*pl);
    if ((*pl)->head == n) {
        *pl = (*pl)->tail;
        return;
    }
    G_nodeList prev = *pl, ns = prev->tail;

    while (ns && ns->head != n) {
        prev = ns;
        ns = ns->tail;
    }
    if (ns && ns->head == n) {
        prev->tail = ns->tail;
    } else {
        assert(0);
    }
}

static G_nodeList nodeListUnion(G_nodeList p, G_nodeList q) {
    G_nodeList r = p; // assume no dup
    for (; q; q = q->tail) {
        if (!findInNodeList(q->head, r)) {
            r = G_NodeList(q->head, r);
        }
    }
    return r;
}

static int nodeListLength(G_nodeList ns) {
    int cnt = 0;
    for (; ns; ns = ns->tail) {
        ++cnt;
    }
    return cnt;
}

static Temp_tempList tempListUnion(Temp_tempList p, Temp_tempList q) {
    Temp_tempList r = p;
    for (; q; q = q->tail) {
        if (!findInTempList(q->head, r)) {
            r = Temp_TempList(q->head, r);
        }
    }
    return r;
}

static G_nodeList getAdjList(G_node n) {
    assert(n);
    return (G_nodeList) G_look(adjList, n);
}

static Live_moveList getMoveList(G_node n) {
    return (Live_moveList) G_look(moveList, n);
}

static void setMoveList(G_node n, Live_moveList ms) {
    assert(n && ms);
    G_enter(moveList, n, (void *) ms);
}

static void adjListAdd(G_node n, G_node adj) {
    assert(n && adj);
    G_enter(adjList, n, (void *) G_NodeList(adj, getAdjList(n)));
}

static bool moveEqual(Live_moveList p, Live_moveList q) {
    if (p->src == q->src && p->dst == q->dst) {
        return TRUE;
    }
    return FALSE;
}

static bool findInMoveList(Live_moveList m, Live_moveList ms) {
    for (; ms; ms = ms->tail) {
        if (moveEqual(m, ms)) {
            return TRUE;
        }
    }
    return FALSE;
}

static void moveListEnter(Live_moveList m, Live_moveList *pl) {
    *pl = Live_MoveList(m->src, m->dst, m->flow, *pl);
}

static void moveListRemove(Live_moveList m, Live_moveList *pl) {
    assert(*pl);
    if (moveEqual(*pl, m)) {
        *pl = (*pl)->tail;
        return;
    }

    Live_moveList prev = *pl, ms = prev->tail;

    while (ms && !moveEqual(m, ms)) {
        prev = ms;
        ms = ms->tail;
    }
    if (moveEqual(m, ms)) {
        prev->tail = ms->tail;
    } else {
        assert(0);
    }
}

static void moveListAdd(G_node n, Live_moveList m) {
    assert(n && m);

    Live_moveList ms = (Live_moveList) G_look(moveList, n);
    moveListEnter(m, &ms);
    assert(ms);
    setMoveList(n, ms);
}

static Live_moveList moveListUnion(Live_moveList p, Live_moveList q) {
    Live_moveList r = p;
    for (; q; q = q->tail) {
        if (!findInMoveList(q, r)) {
            moveListEnter(q, &r);
        }
    }
    return r;
}

static bool *adjSetAt(G_node p, G_node q) {
    int i = G_nodeKey(p), j = G_nodeKey(q);
    assert(adjSet && i < adjSetDim && j < adjSetDim);
    return adjSet + i * adjSetDim + j;
}

static void printRig() {
    DEBUG_PRINT("-----------rig-------------\n");
    G_nodeList ns = G_nodes(rig);

    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        G_nodeList q = getAdjList(n);
        DEBUG_PRINT(">>%s:", nodeName(n));
        for (; q; q = q->tail) {
            DEBUG_PRINT("%s ", nodeName(q->head));
        }
        DEBUG_PRINT("\n");
    }
    DEBUG_PRINT("--------end rig-------------\n");
}


static void initOnce() {
    static bool done;
    if (done) return;
    done = TRUE;
    regs = F_getRegList();
}

static G_node rigNode(Temp_temp t) {
    G_node n = (G_node) Temp_look(gtemp, t);
    if (n) {
        return n;
    }
    n = G_Node(rig, t);
    assert(tempName(t));
    Temp_enter(gtemp, t, (string) n);
    assert(nodeName(n));
    return n;
}

static void addEdge(G_node u, G_node v) {
    if (*adjSetAt(u, v) || u == v) {
        return;
    }
    *adjSetAt(u, v) = *adjSetAt(v, u) = TRUE;
    if (!isPrecolored(u)) {
        setDegree(u, 1 + getDegree(u));
        adjListAdd(u, v);
    }
    if (!isPrecolored(v)) {
        setDegree(v, 1 + getDegree(v));
        adjListAdd(v, u);
    }
}

static G_nodeList adjacent(G_node n) {
    G_nodeList r = NULL, adjs = getAdjList(n);
    G_nodeList ns = selectStack;
    for (; adjs; adjs = adjs->tail) {
        G_node adj = adjs->head;
        if (findInNodeList(adj, selectStack) || findInNodeList(adj, coalescedNodes)) {
            continue;
        }
        r = G_NodeList(adj, r);
    }
    return r;
}

static Live_moveList nodeMoves(G_node n) {
    Live_moveList r = NULL, ms = getMoveList(n);
    for (; ms; ms = ms->tail) {
        if (findInMoveList(ms, activeMoves) || findInMoveList(ms, worklistMoves)) {
            moveListEnter(ms, &r);
        }
    }
    return r;
}

static bool moveRelated(G_node n) {
    return nodeMoves(n) != NULL;
}

static void enableMoves(G_nodeList ns) {
    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        Live_moveList ms = nodeMoves(n);
        for (; ms; ms = ms->tail) {
            Live_moveList m = ms;
            if (findInMoveList(m, activeMoves)) {
                moveListRemove(m, &activeMoves);
                moveListEnter(m, &worklistMoves);
            }
        }
    }
}

static void freezeMoves(G_node u) {
    Live_moveList ms = nodeMoves(u);
    for (; ms; ms = ms->tail) {
        Live_moveList m = ms;
        G_node x = m->src, y = m->dst, v;
        if (getAlias(y) == getAlias(u)) {
            v = getAlias(x);
        } else {
            v = getAlias(y);
        }

        moveListRemove(m, &activeMoves);
        moveListEnter(m, &frozenMoves);

        if (nodeMoves(v) || getDegree(v) >= F_numReg || isPrecolored(v)) {
            continue;
        }
        nodeListRemove(v, &freezeWorklist);
        nodeListEnter(v, &simplifyWorklist);
    }
}

static void decrementDegree(G_node m) {

    if (isPrecolored(m)) return;
    int d = getDegree(m);
    assert(d > 0);
    setDegree(m, d - 1);
    if (d != F_numReg || isPrecolored(m) /*|| !findInNodeList(m, spillWorklist)*/) {
        return;
    }
    assert(findInNodeList(m, spillWorklist));

    enableMoves(G_NodeList(m, adjacent(m)));
    nodeListRemove(m, &spillWorklist);

    if (moveRelated(m)) {
        nodeListEnter(m, &freezeWorklist);
    } else {
        nodeListEnter(m, &simplifyWorklist);
    }
}

static bool ok(G_node t, G_node r) {
    return getDegree(t) < F_numReg || isPrecolored(t) || *adjSetAt(t, r);
}

static bool conservative(G_nodeList ns) {
    int k = 0;
    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        if (getDegree(n) >= F_numReg) ++k;
    }
    return k < F_numReg;
}

static void addWorklist(G_node u) {
    if (!isPrecolored(u)) assert(findInNodeList(u, freezeWorklist) || findInNodeList(u, spillWorklist));
    if (isPrecolored(u) || moveRelated(u) || getDegree(u) >= F_numReg) {
        return;
    }
    nodeListRemove(u, &freezeWorklist);
    nodeListEnter(u, &simplifyWorklist);
}

static void combine(G_node u, G_node v) {
    assert(!isPrecolored(v) && (findInNodeList(v, freezeWorklist) || findInNodeList(v, spillWorklist)));
    if (findInNodeList(v, freezeWorklist)) {
        nodeListRemove(v, &freezeWorklist);
    } else {
        nodeListRemove(v, &spillWorklist);
    }
    nodeListEnter(v, &coalescedNodes);
    setAlias(v, u);
    setMoveList(u, moveListUnion(getMoveList(u), getMoveList(v)));

    G_nodeList adjs = adjacent(v);
    for (; adjs; adjs = adjs->tail) {
        G_node t = adjs->head;
        int d = getDegree(t);
        if (d == F_numReg - 1) {
            decrementDegree(t);
            addEdge(t, u);
        } else {
            addEdge(t, u);
            decrementDegree(t);
        }
    }
    if (getDegree(u) >= F_numReg && findInNodeList(u, freezeWorklist)) {
        nodeListRemove(u, &freezeWorklist);
        nodeListEnter(u, &spillWorklist);
    }
}

static void simplify() {
    G_node n = simplifyWorklist->head;
    assert(!isPrecolored(n));
    nodeListRemove(n, &simplifyWorklist);
    nodeListEnter(n, &selectStack);

    G_nodeList adjs = adjacent(n);
    for (; adjs; adjs = adjs->tail) {
        G_node m = adjs->head;
        assert(getDegree(m) > 0 || isPrecolored(m));
        if (!isPrecolored(m)) {
            decrementDegree(m);
        }
    }
}

static void freeze() {
    G_node u = freezeWorklist->head;
    nodeListRemove(u, &freezeWorklist);
    nodeListEnter(u, &simplifyWorklist);
    freezeMoves(u);
}

static G_node selectNodeForSpill() {
    G_nodeList ns;
    G_node minNode = NULL;
    double min = 0.0;//getSpillCost(minNode);
    bool noSpilled = TRUE;
redo:
    ns = spillWorklist;
    assert(ns);
    for (ns = ns->tail; ns; ns = ns->tail) {
        if (noSpilled && findInTempList(G_nodeInfo(ns->head), spilledTemps)) {
            continue;
        }
        int c = getSpillCost(ns->head);
        if (!minNode || c < min) {
            c = min;
            minNode = ns->head;
        }
    }
    if (!minNode) {
        noSpilled = FALSE;
        goto redo;
    }
    return minNode;
}

static void selectSpill() {
    G_node m = selectNodeForSpill();
    nodeListRemove(m, &spillWorklist);
    nodeListEnter(m, &simplifyWorklist);
    freezeMoves(m);
}


static bool anyAdjacentOk(G_node v, G_node u) {
    G_nodeList adjs = adjacent(v);
    for (; adjs; adjs = adjs->tail) {
        G_node t = adjs->head;
        if (!ok(t, u)) {
            return FALSE;
        }
    }
    return TRUE;
}

static void coalesce() {
    Live_moveList m = worklistMoves;

    G_node x = getAlias(m->src), y = getAlias(m->dst), u, v;

    if (isPrecolored(y)) {
        u = y;
        v = x;
    } else {
        u = x;
        v = y;
    }

    moveListRemove(m, &worklistMoves);

    if (u == v) {
        moveListEnter(m, &coalescedMoves);
        addWorklist(u);
    } else if (isPrecolored(v) || *adjSetAt(u, v)) {
        moveListEnter(m, &constrainedMoves);
        addWorklist(u);
        addWorklist(v);
    } else if ((isPrecolored(u) && anyAdjacentOk(v, u))
               || (!isPrecolored(u) && conservative(nodeListUnion(adjacent(u), adjacent(v))))) {
        moveListEnter(m, &coalescedMoves);
        combine(u, v);
        addWorklist(u);
    } else {
        moveListEnter(m, &activeMoves);
    }
}

static void initContext() {
    rig = G_Graph();

    simplifyWorklist = freezeWorklist = spillWorklist = spilledNodes = coalescedNodes = coloredNodes = selectStack = NULL;
    coalescedMoves = constrainedMoves = frozenMoves = worklistMoves = activeMoves = NULL;

    adjList = G_empty();
    degree = G_empty();
    alias = G_empty();
    color = G_empty();
    moveList = G_empty();
    cost = G_empty();

    gtemp = Temp_empty();
}

static void increaseSpillCost(G_node n) {
    setSpillCost(n, 1 + getSpillCost(n));
}

static void buildRig() {
    G_nodeList ns = G_nodes(flow);

    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        Temp_tempList defs = FG_def(n);
        for (; defs; defs = defs->tail) {
            Temp_temp def = defs->head;
            rigNode(def); // create;
        }
    }

    adjSetDim = nodeListLength(G_nodes(rig));
    assert(adjSetDim > 0);
    adjSet = calloc(adjSetDim * adjSetDim, 1);

    ns = G_nodes(flow);
    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        Temp_tempList defs = FG_def(n), uses = FG_use(n);
        Temp_temp exclude = NULL;
        if (FG_isMove(n)) {
            assert(defs && !defs->tail && uses && !uses->tail);
            Temp_temp def = defs->head, use = uses->head;
            exclude = use;
            Live_moveList m = Live_MoveList(rigNode(use), rigNode(def), n, NULL);
            moveListAdd(rigNode(def), m);
            if (def != use) {
                moveListAdd(rigNode(use), m);
            }
            moveListEnter(m, &worklistMoves);
        }

        for (; defs; defs = defs->tail) {
            Temp_temp def = defs->head;

            Temp_tempList lives = (Temp_tempList) G_look(liveOut, n);
            for (; lives; lives = lives->tail) {
                Temp_temp live = lives->head;
                if (live == exclude) {
                    continue;
                }
                G_node nd = rigNode(def), nl = rigNode(live);
                addEdge(nd, nl);
                if (!isPrecolored(nd)) {
                    increaseSpillCost(nd);
                }
                if (!isPrecolored(nl)) {
                    increaseSpillCost(nl);
                }
            }
        }
    }

}

static void initSpillCosts() {
    G_nodeList ns = G_nodes(rig);

    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        if (isPrecolored(n)) continue;
        int len = nodeListLength(getAdjList(n));
        if (!len) continue;
        setSpillCost(n, getSpillCost(n) / len);
    }
}

static void build() {
    initContext();
    flow = FG_AssemFlowGraph(instrList, frame);
    liveOut = Live_liveness(flow);
    buildRig();
    initSpillCosts();
}

static void makeWorklist() {
    G_nodeList ns = G_nodes(rig);

    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        if (isPrecolored(n)) {
            continue;
        }

        if (getDegree(n) >= F_numReg) {
            nodeListEnter(n, &spillWorklist);
        } else if (moveRelated(n)) {
            nodeListEnter(n, &freezeWorklist);
        } else {
            nodeListEnter(n, &simplifyWorklist);
        }
    }
}

static Temp_temp pickColor(G_nodeList adjs) {
    Temp_tempList colors = regs;
    for (; colors; colors = colors->tail) {
        Temp_temp c = colors->head;
        G_nodeList ns = adjs;
        bool used = FALSE;
        for (; ns; ns = ns->tail) {
            G_node n = ns->head;
            if (getColor(getAlias(n)) == c) {
                used = TRUE;
                break;
            }
        }
        if (!used) {
            return c;
        }
    }
    return NULL;
}

static G_nodeList getAliasedNodes(G_node n) {
    G_nodeList ns = coalescedNodes;
    G_nodeList r = NULL;
    for (; ns; ns = ns->tail) {
        G_node a = ns->head;
        if (getAlias(a) == n) {
            nodeListEnter(a, &r);
        }
    }
    return r;
}

static void assignColor(G_node n) {
    G_nodeList adjs = getAdjList(n);

    G_nodeList aliasedNodes = getAliasedNodes(n);
    printNodeList(aliasedNodes);
    for (; aliasedNodes; aliasedNodes = aliasedNodes->tail) {
        G_node aliased = aliasedNodes->head;
        G_nodeList aliasedAdjs = getAdjList(aliased);
        printNodeList(aliasedAdjs);
        adjs = nodeListUnion(adjs, aliasedAdjs);
    }

    printNodeList(adjs);
    Temp_temp c = pickColor(adjs);

    if (!c) {
        nodeListEnter(n, &spilledNodes);
    } else {
        nodeListEnter(n, &coloredNodes);
        setColor(n, c);
    }
}


static void assignColors() {
    for (; selectStack; selectStack = selectStack->tail) {
        G_node n = selectStack->head;
        assignColor(n);
    }

    G_nodeList ns = coalescedNodes;
    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        Temp_temp c = getColor(getAlias(n));
        if (c)
        setColor(n, c);
    }
}

static void replaceTempList(Temp_tempList list, Temp_temp from, Temp_temp to) {
    for (; list; list = list->tail) {
        if (list->head == from) list->head = to;
    }
}


static void rewriteSpill(Temp_temp temp, int offset) {
    AS_instrList il = instrList;
    Temp_temp prevSpilled;
    for (; il; il = il->tail) {
        AS_instr instr = il->head, before = NULL, after = NULL;
        Temp_tempList defs = AS_def(instr), uses = AS_use(instr);

        if (defs && uses && defs->head == uses->head) continue;

        if (findInTempList(temp, defs)) {
            char buf[256];
            sprintf(buf, "movl `s0, %d(`s1) # store %s", offset, tempName(temp));
            AS_instr newInstr = AS_Oper(buf, NULL, Temp_TempList(temp, Temp_TempList(F_FP(), NULL)), NULL);
            prevSpilled = temp;
            after = newInstr;
        } else {
            prevSpilled= NULL;
        }

        bool skipUse = FALSE;
        if (temp == prevSpilled) {
            skipUse = TRUE;
        }

        if (!skipUse && findInTempList(temp, uses)) {
            

            char buf[256];
            Temp_temp t = Temp_newtemp();
            sprintf(buf, "movl %d(`s0), `d0 # load %s", offset, tempName(temp));
            spilledTemps = Temp_TempList(t, spilledTemps);
            replaceTempList(uses, temp, t);

            AS_instr newInstr = AS_Oper(buf, Temp_TempList(t, NULL), Temp_TempList(F_FP(), NULL), NULL);
            before = newInstr;
        }

        if (before) {
            il->tail = AS_InstrList(il->head, il->tail);
            il->head = before;
            il = il->tail;
        }
        if (after) {
            il->tail = AS_InstrList(after, il->tail);
            il = il->tail;
        }
    }
}


static void rewriteProgram() {
    G_nodeList ns = spilledNodes;
    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        Temp_temp spill = G_nodeInfo(n);
        int stackLoc = F_allocInStack(frame);
        rewriteSpill(spill, stackLoc);
    }
}

static Temp_map buildTempMap() {
    Temp_map regMap = F_regTempMap();

    Temp_map map = Temp_empty();
    G_nodeList ns = G_nodes(rig);

    for (; ns; ns = ns->tail) {
        G_node n = ns->head;
        Temp_temp temp = (Temp_temp) G_nodeInfo(n);
        Temp_temp reg = getColor(n);
        assert(reg);
        string regName = Temp_look(regMap, reg);
        Temp_enter(map, temp, regName);
    }

    return map;
}

static void printInstrList() {
    AS_instrList il = instrList;
    for (; il; il = il->tail) {
        printInstr(il->head);
    }
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
    struct RA_result ret;

    frame = f;
    instrList = il;

    initOnce();

redo:
    build();
    makeWorklist();
    while (simplifyWorklist || worklistMoves || freezeWorklist || spillWorklist) {
        if (simplifyWorklist) {
            simplify();
        } else if (worklistMoves) {
            coalesce();
        } else if (freezeWorklist) {
            freeze();
        } else if (spillWorklist) {
            selectSpill();
        }
    }
    assignColors();
    if (spilledNodes) {
        rewriteProgram();
        goto redo;
    }

    ret.coloring = buildTempMap();
    ret.il = instrList;
    return ret;
}

    
