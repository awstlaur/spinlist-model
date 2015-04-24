// Each test case will #include this file and give their own init.

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

#define CHECK_NODE_VALID(id) assert(id >= 0 && id < NUM_NODES &&       \
                                    NODE(id).this == id)

#define ASSERT_VALID_DATA(dat) assert(DATA_MIN <= (dat) && DATA_MAX >= (dat))

// Waits for the list to be initialized. Must do this before performing actions.
#define WAIT_FOR_INITIALIZATION  \
    do                           \
        :: initialized -> break; \
        :: else -> skip;         \
    od

// Use this to stop the simulation.
#define SHUTDOWN() shutdown = true

#define DESTROY_INVALID_NODE(id)  \                         \
    assert(NODE(id).this == id);  \
    node_gen!id

#define DESTROY_NODE(id)          \
    CHECK_NODE_VALID(id);         \
    DESTROY_INVALID_NODE(id)

// uninitialized link
#define NIL -1

typedef Node {
    NODE_ID this;
    NODE_ID link;
    bool mark;
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
    for (cur in nodes) {
        NODE(cur).this = cur;
        NODE(cur).link = NIL;
        NODE(cur).mark = false;
        node_gen!cur;
    }

    // ?? pulls the id out no mater its place.
    // Used so that head is 0 and tail is NUM_NODES - 1
    node_gen??eval(head);
    node_gen??eval(tail);

    NODE(head).link = tail;
    NODE(head).data = NEG_INF;
    NODE(tail).data = POS_INF;
    printf("Head is node %d\nTail is node %d\n", head, tail);
    initialized = true;
}

// Will search for the value, checking consistancy as it goes.
// Will not return anything...
proctype search(int value, bool sorted) {
    ASSERT_VALID_DATA(value);
    WAIT_FOR_INITIALIZATION;
    // TODO allight
}

proctype push(int value){
    // TODO awstlaur
}

proctype pop(){
    // TODO awstlaur
}

proctype append(int value){
    // TODO awstlaur
}

proctype insert_sorted(int value){
    // TODO allight
}

proctype remove_sorted(int value){
    // TODO allight
}
