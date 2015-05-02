/* Each test case will #include this file and give their own init. */

/* Maximum number of nodes, Including -inf and +inf nodes */
#define NUM_NODES 12

/* What we allow data in the list to be between */
#define DATA_MIN -100
#define DATA_MAX 100
#define NEG_INF (DATA_MIN - 1)
#define POS_INF (DATA_MAX + 1)

#define NODE_ID int

/* Gets a node from an id. Use this everywhere. */
#define NODE(id) nodes[(id)]

#define CHECK_NODE_VALID(id) assert(id >= 0 && id < NUM_NODES && \
                                    NODE(id).this == id)

#define ASSERT_VALID_DATA(dat) assert(DATA_MIN <= (dat) && DATA_MAX >= (dat))

/* Waits for the list to be initialized. Must do this before performing actions. */
#define WAIT_FOR_INITIALIZATION() \
    if                           \
        :: initialized \
    fi; \
    assert(initialized) \


/* Use this to stop the simulation. */

#define DESTROY_INVALID_NODE(id)  \
    assert(NODE(id).this == id);  \
    NODE(id).gen += 1;            \
    NODE(id).mark = false;        \
    NODE(id).link = NIL;          \
    node_gen!id;

#define DESTROY_NODE(id)          \
    atomic {                      \
        CHECK_NODE_VALID(id);     \
        DESTROY_INVALID_NODE(id); \
    }

#define GOTO_ON_FAIL(prop, labl) \
    if \
        :: !(prop) -> printf("prop failed\n"); goto labl; \
        :: else \
    fi

#define FIND_OP(v)                                                    \
    NODE_ID pred;                                                     \
    int p_gen;                                                        \
    NODE_ID curr;                                                     \
    int c_gen;                                                        \
    NODE_ID succ;                                                     \
    int s_gen;                                                        \
    bool marked = false;                                              \
retry:                                                                \
    pred = NIL; \
    p_gen = NIL; \
    curr = NIL; \
    c_gen = NIL; \
    succ = NIL; \
    s_gen = NIL; \
    /* Start of find operation. pred, cur is the window. */           \
    atomic {                                                          \
        pred = head;                                                  \
        p_gen = NODE(pred).gen;                                       \
    }                                                                 \
    atomic {                                                          \
        curr = NODE(pred).link;                                       \
        c_gen = NODE(curr).gen;                                       \
    }                                                                 \
    /* pred == head so it should never change. */                     \
    assert(NODE(pred).gen == 0);                                      \
    do                                                                \
        :: NODE(curr).data >= (v) -> \
            atomic { \
                printf("found node %d with data %d\n", curr, NODE(curr).data); \
            } \
            break;                                                    \
        :: else ->                                                    \
            assert(curr != tail);                                     \
            atomic {                                                  \
                succ = NODE(curr).link;                               \
                GOTO_ON_FAIL(succ != NIL, retry);                     \
                GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);         \
                s_gen = NODE(succ).gen;                               \
            }                                                         \
            /* We will let remove be the only one to delete stuff. */ \
            GOTO_ON_FAIL(NODE(succ).mark == false, retry);            \
            pred = curr;                                              \
            p_gen = c_gen;                                            \
            curr = succ;                                              \
            c_gen = s_gen;                                            \
    od;                                                               \
    /* End of find operation */                                       \

/* uninitialized link */
#define NIL -1

typedef Node {
    NODE_ID this;
    NODE_ID link;
    bool mark;
    int data;
    /* The generation. We should check this to make sure that the node is not
     * destroyed while we are doing a call.  We need this since we lack a
     * tracing garbage collector
     */
    int gen;
}

Node nodes[NUM_NODES];

/* Each process will read from this to get a Node */
chan node_gen = [NUM_NODES] of { NODE_ID };

/* Head & tail */
NODE_ID head = 0;
NODE_ID tail = (NUM_NODES - 1);
bool initialized = false;

/* This process fills the node_gen and initialized head and tail.
 * It must be run by init in whatever test we use.
 */
proctype init_nodes() {
    assert(!initialized);
    NODE_ID cur = 0;
    for (cur in nodes) {
        NODE(cur).this = cur;
        NODE(cur).link = NIL;
        NODE(cur).mark = false;
        NODE(cur).gen = 0;
        node_gen!cur;
    }

    /* ?? pulls the id out no mater its place.
     * Used so that head is 0 and tail is NUM_NODES - 1
     */
    node_gen??eval(head);
    node_gen??eval(tail);

    NODE(head).link = tail;
    NODE(head).data = NEG_INF;
    NODE(tail).data = POS_INF;
    NODE(tail).link = NIL;
    printf("Head is node %d\nTail is node %d\n", head, tail);
    initialized = true;
}

/* Will search for the value, checking consistancy as it goes.
 * Will not return anything... */
proctype search_sorted(int value) {
    ASSERT_VALID_DATA(value);

    FIND_OP(value);
    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        if  :: NODE(curr).data == value -> printf("Found %d in node %d\n", value, curr);
            :: else -> printf("Unable to find %d\n", value);
        fi
    }
}

/* pushes a new node onto the list.
 * new node becomes head.
 */
proctype push(int value){

    ASSERT_VALID_DATA(value);

    NODE_ID id;
    node_gen?id;
    CHECK_NODE_VALID(id);

    NODE(id).data = value;

    NODE_ID prev_head = head;
    NODE(id).link = prev_head;
    head = NODE(id).this;

    /* TODO (awstlaur)
     * what needs to be in an atomic block?
     */    

}

/* puts a new node at the end of the list.
 * new node becomes tail.
 */
proctype append(int value){
    ASSERT_VALID_DATA(value);

    NODE_ID id;
    node_gen?id;
    CHECK_NODE_VALID(id);
    /* TODO (awstlaur)
     * finish */
}

/* removes the "head" element
 *   from the list
 */
proctype pop(){
     NODE_ID prev_head = head;
     head = head.link;
     DESTROY_NODE(prev_head);
     /* TODO (awstlaur)
      * can't think of what else a.t.m.
      * besides, maybe, using an
      * atomic block if needed?
      */
}

proctype insert_sorted(int value){
    ASSERT_VALID_DATA(value);
    NODE_ID new_node;

    /* Get a new node which will be inserted. This will block until one is availible. */
    node_gen?new_node;

    FIND_OP(value);

    CHECK_NODE_VALID(pred);
    CHECK_NODE_VALID(curr);

    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        if
            :: NODE(curr).data == value -> printf("%d is already in the list, skipping\n", value); goto finish;
            :: else
        fi
    }
    NODE(new_node).data = value;
    NODE(new_node).link = curr;
    NODE(new_node).mark = false;
    atomic {
        /* Make sure pred & curr have not been deleted. */
        GOTO_ON_FAIL(NODE(pred).gen == p_gen, retry);
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        if
            :: (NODE(pred).link == curr && !NODE(pred).mark && !NODE(curr).mark) ->
                NODE(pred).link = new_node;
                printf("%d inserted into list\n", value);
                goto finish;
            :: else ->
                printf("CAS Failed, p == %d p.link == %d curr == %d pmark = %d cmark = %d\n",
                       pred, NODE(pred).link, curr, NODE(pred).mark, NODE(curr).mark);
                goto retry;
        fi
    }

finish:
    printf("insert of %d finished\n", value);
}

proctype remove_sorted(int value) {
    ASSERT_VALID_DATA(value);

    FIND_OP(value);

    CHECK_NODE_VALID(pred);
    CHECK_NODE_VALID(curr);
    assert(curr != tail);

    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        if
            :: NODE(curr).data != value -> printf("%d is not in the list, skipping\n", value); goto finish;
            :: else
        fi
    }
    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        succ = NODE(curr).link;
        s_gen = NODE(succ).gen;
    }
finish:
    printf("remove of %d finished\n", value);
    /* TODO allight */
}


proctype check_sorted() {
    atomic {
        int l = 0;
        NODE_ID cur = head;
        bool seen[NUM_NODES];
        int i;
        for (i in seen) {
            seen[i] = false;
        };
        do
            :: (cur != tail)  ->
                CHECK_NODE_VALID(cur);
                CHECK_NODE_VALID(NODE(cur).link);
                assert(NODE(cur).data < NODE(NODE(cur).link).data);
                assert(!seen[cur]);
                seen[cur] = true;
                cur = NODE(cur).link;
                l = l + 1;
            :: else -> break;
        od;
        printf("List of length %d is currently sorted correctly\n", l - 1);
    }
}


