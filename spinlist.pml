// Each test case will #include this file and give their own init.

// How many levels the spinlist has
#define NUM_LINKS 3

// Maximum number of nodes, Including -inf and +inf nodes
#define NUM_NODES 12

// What we allow data in the list to be between
#define DATA_MIN -100
#define DATA_MAX 100
#define NEG_INF (DATA_MIN - 1)
#define POS_INF (DATA_MAX + 1)

#define NODE_ID int

// Gets a node from an id. Use this everywhere.
#define NODE(id) (nodes[(id)])

#define CHECK_NODE_VALID(id) assert(NODE(id).this == id &&             \
                                    NODE(id).num_levels != NIL &&      \
                                    NODE(id).num_levels < NUM_LINKS && \
                                    NODE(id).num_levels >= 0)

// Waits for the list to be initialized. Must do this before performing actions.
#define WAIT_FOR_INITIALIZATION  \
    do                           \
        :: initialized -> break; \
        :: else -> skip;         \
    od

// Use this to stop the simulation.
#define SHUTDOWN() shutdown = true

#define DESTROY_INVALID_NODE(id)  \
    NODE(id).num_levels = NIL;    \
    for (a in NODE(id).link) {    \
        NODE(id).link[a] = NIL;   \
        NODE(id).mark[a] = false; \
    }                             \
    assert(NODE(id).this == id);  \
    node_gen!id

#define DESTROY_NODE(id)          \
    CHECK_NODE_VALID(id);         \
    DESTROY_INVALID_NODE(id)

// What the link is set to if we do not have a next at that level.
#define NIL -1

typedef Node {
    NODE_ID this;
    NODE_ID link[NUM_LINKS];
    bool marks[NUM_LINKS];
    // Number of levels in this node, being set to NIL indicates this node is not initialized.
    int num_levels;
    int data;
}

Node nodes[NUM_NODES];

// Each process will read from this to get a Node
chan node_gen = [NUM_NODES] of { NODE_ID };

// Head & tail
NODE_ID head = 0;
NODE_ID tail = (NUM_NODES - 1);
bool initialized = false;
bool shutdown = false;

// This process fills the node_gen and initialized head and tail. It must be run by init in whatever test we use.
proctype init_nodes() {
    assert(!initialized);
    NODE_ID cur = 0;
    int lvl = 0;
    for (cur in nodes) {
        NODE(cur).this = cur;
        NODE(cur).num_levels = NIL;
        // Set all links to NIL
        for (lvl in NODE(cur).link) {
            NODE(cur).link[lvl] = NIL;
            NODE(cur).mark[lvl] = false;
        }
        node_gen!cur;
    }

    // ?? pulls the id out no mater its place.
    // Used so that head is 0 and tail is NUM_NODES - 1
    node_gen??eval(head);
    node_gen??eval(tail);

    NODE(head).num_levels = NUM_LINKS;
    NODE(tail).num_levels = NUM_LINKS;
    NODE(head).data = NEG_INF;
    NODE(tail).data = POS_INF;
    // Link the head to the tail
    for (lvl in NODE(head).link) {
        NODE(head).link[lvl] = tail;
    }
    printf("Head is node %d\nTail is node %d\n", head, tail);
    initialized = true;
}
