
// How many levels the spinlist has
#define NUM_LINKS 3
// Maximum number of nodes, Including -inf and +inf nodes
#define NUM_NODES 12
// What we allow data in the list to be between
#define DATA_MIN -100
#define DATA_MAX 100

typedef Node {
    int link[NUM_LINKS];
    int data;
    int allocated;
}

Node nodes[NUM_NODES];
