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
    if                            \
        :: initialized            \
    fi;                           \
    assert(initialized)           \


/* Use this to stop the simulation. */

#define DESTROY_INVALID_NODE(id)  \
    assert(NODE(id).this == id);  \
    NODE(id).gen++;               \
    NODE(id).mark = false;        \
    NODE(id).link = NIL;          \
    NODE(id).data = 0;            \
    node_gen!id;

#define DESTROY_NODE(id)          \
    atomic {                      \
        CHECK_NODE_VALID(id);     \
        DESTROY_INVALID_NODE(id); \
    }

#define GOTO_ON_FAIL(prop, labl)                                        \
    if                                                                  \
        :: !(prop) -> printf("prop %d failed\n", __LINE__ ); goto labl; \
        :: else                                                         \
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
    pred = NIL;                                                       \
    p_gen = NIL;                                                      \
    curr = NIL;                                                       \
    c_gen = NIL;                                                      \
    succ = NIL;                                                       \
    s_gen = NIL;                                                      \
    /* Start of find operation. pred, cur is the window. */           \
    atomic {                                                          \
        printf("FIND_OP atomic block 1\n");                           \
        pred = head;                                                  \
        p_gen = NODE(pred).gen;                                       \
    }                                                                 \
    atomic {                                                          \
        printf("FIND_OP atomic block 2\n");                           \
        curr = NODE(pred).link;                                       \
        c_gen = NODE(curr).gen;                                       \
        printf("(FIND_OP) curr = %d, pred = %d\n", curr, pred);       \
    }                                                                 \
    /* pred == head so it should never change. */                     \
    assert(NODE(pred).gen == 0);                                      \
    do                                                                \
        :: NODE(curr).mark -> printf("NODE(%d).mark = true\n", curr); \
            goto retry;                                               \
        :: NODE(curr).data >= (v) ->                                  \
            atomic {                                                  \
                printf("FIND_OP atomic block 3\n");                   \
                GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);         \
                printf("found node %d with data %d\n",                \
                        curr, NODE(curr).data);                       \
            }                                                         \
            break;                                                    \
        :: else ->                                                    \
            assert(curr != tail);                                     \
            atomic {                                                  \
                printf("FIND_OP atomic block 4\n");                   \
                succ = NODE(curr).link;                               \
                GOTO_ON_FAIL(succ != NIL, retry);                     \
                GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);         \
                s_gen = NODE(succ).gen;                               \
            }                                                         \
            /* We will let remove be the only one to delete stuff. */ \
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
chan node_gen = [NUM_NODES - 2] of { NODE_ID };

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
    for (cur : (head + 1) .. (tail - 1)) {
        NODE(cur).this = cur;
        NODE(cur).link = NIL;
        NODE(cur).mark = false;
        NODE(cur).gen = 0;
        node_gen!cur;
        /*if  :: cur != head && cur != tail -> node_gen!cur;
            :: else;
        fi;*/
    }

    /* ?? pulls the id out no mater its place.
     * Used so that head is 0 and tail is NUM_NODES - 1
     */

    NODE(head).this = head;
    NODE(tail).this = tail;

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
    printf("(push) new node id = %d\n", id);
    NODE(id).data = value;
    NODE(id).mark = false;

retry_push:
    NODE(id).link = NODE(head).link;
    atomic {
        printf("(push) atomic block 1\n")
        GOTO_ON_FAIL(NODE(id).link == NODE(head).link, retry_push);
        GOTO_ON_FAIL(!NODE(NODE(head).link).mark, retry_push);
        GOTO_ON_FAIL((NODE(NODE(id).link).gen == NODE(NODE(head).link).gen), retry_push);
        NODE(head).link = NODE(id).this;
        printf("push(%d) finished\n", value);
        int i;
        for (i in nodes) {
            printf("(push)    nodes[%d].link = %d\n", i, nodes[i].link)
        }
    }

}

/* puts a new node at the end of the list.
 * new node becomes tail.
 */
proctype append(int value){
    atomic{printf("append(%d) starting\n", value);}

    ASSERT_VALID_DATA(value);

    NODE_ID id;
    node_gen?id;    
    CHECK_NODE_VALID(id);
    printf("(append) new node id = %d\n", id);
    NODE(id).data = value;
    NODE(id).mark = false;

/*retry:*/  
    /* find the tail, store id in curr. 
     * NODE(pred).link -> tail
     */
    FIND_OP(POS_INF);
    /* because NODE(curr) is the tail */
    assert(NODE(curr).gen == 0);
    printf("(append) FIND_OP gives curr: %d\n", curr);
    printf("(append) FIND_OP gives pred: %d\n", pred);

    CHECK_NODE_VALID(pred);
    CHECK_NODE_VALID(curr);

    NODE(pred).link = NODE(id).this;

    atomic {
        printf("(append) atomic block 1\n")
        GOTO_ON_FAIL(NODE(pred).gen == p_gen, retry);
        GOTO_ON_FAIL(!NODE(pred).mark, retry);      
        NODE(id).link = tail;
        printf("append(%d) finished", value);
        int i;
        for (i in nodes) {
            printf("(append)    nodes[%d].link = %d\n", i, nodes[i].link)
        }
    }


}

/* removes the "head" element from the list.
 * blocks until the list is non-empty.
 */
proctype pop(){
    printf("pop start\n");
retry_pop:    
    if
        :: NODE(head).link != tail ->
            NODE_ID curr;
            NODE_ID succ;
            int c_gen;
            int s_gen;

            atomic {
                printf("(pop) atomic block 1\n")
                curr = NODE(head).link;
                c_gen = NODE(curr).gen;
                printf("(pop) curr = %d\n", curr);
            }
            
            atomic {
                printf("(pop) atomic block 2\n")
                GOTO_ON_FAIL(NODE(curr).gen == c_gen, finish_pop);
                succ = NODE(curr).link;
                printf("(pop) succ = %d\n", succ);
                /*printf("NODE(curr).this = %d ::: NODE(tail).this = %d\n", NODE(curr).this, NODE(tail).this)*/
                GOTO_ON_FAIL(NODE(curr).this != NODE(tail).this, retry_pop);
                s_gen = NODE(succ).gen;
            }

            atomic {
                printf("(pop) atomic block 3\n")
                GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry_pop);
                GOTO_ON_FAIL(NODE(succ).gen == s_gen, retry_pop);
                printf("(pop) marking phase:\n");
                printf("(pop)     curr = %d, curr.mark = %d, curr.link = %d\n", curr, NODE(curr).mark, NODE(curr).link);
                printf("(pop)     succ = %d, succ.mark = %d\n", succ, NODE(succ).mark);
                printf("(pop)     curr.gen, = %d, c_gen = %d\n", NODE(curr).gen, c_gen);
                printf("(pop)     succ.gen, = %d, s_gen = %d\n", NODE(succ).gen, s_gen);
                if  :: !(NODE(curr).mark) && (NODE(curr).link == succ) && (NODE(succ).gen == s_gen) -> 
                        NODE(curr).mark = true;
                    :: NODE(curr).mark && NODE(curr).link == succ && NODE(succ).gen == s_gen -> 
                        goto finish_pop;
                    :: else -> 
                        printf("marking failed for pop (of node w/value %d)\n", NODE(curr).data); 
                        goto retry_pop;
                fi;
            }
            atomic {
                printf("(pop) atomic block 4\n")
                GOTO_ON_FAIL(NODE(succ).gen == s_gen, retry_pop);
                GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry_pop);
                printf("(pop) destroy phase:\n");
                printf("(pop)     curr = %d, curr.mark = %d, curr.link = %d\n", curr, NODE(curr).mark, NODE(curr).link);
                printf("(pop)     succ = %d, succ.mark = %d\n", succ, NODE(succ).mark);
                printf("(pop)     curr.gen, = %d, c_gen = %d\n", NODE(curr).gen, c_gen);
                printf("(pop)     succ.gen, = %d, s_gen = %d\n", NODE(succ).gen, s_gen);
                if  :: NODE(head).link == curr -> NODE(head).link = succ;
                    :: else -> goto finish_pop;
                fi;

                DESTROY_NODE(curr);
            }
    fi;

finish_pop:
    printf("pop finished\n");
    int i;
    for (i in nodes) {
        printf("(pop)    nodes[%d].link = %d\n", i, nodes[i].link)
    }
}

proctype insert_sorted(int value){
    ASSERT_VALID_DATA(value);
    NODE_ID new_node;

    /* Get a new node which will be inserted. This will block until one is availible. */
    node_gen?new_node;
    assert(NODE(new_node).link == NIL);

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

    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        if
            :: NODE(curr).data != value -> printf("%d is not in the list, skipping\n", value); goto finish;
            :: else
        fi
    }
    // Get the successor
    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, finish);
        succ = NODE(curr).link;
        s_gen = NODE(succ).gen;
    }
    // Do the marking.
    atomic {
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        if  :: !(NODE(curr).mark) && NODE(curr).link == succ && NODE(succ).gen == s_gen -> NODE(curr).mark = true;
            :: NODE(curr).mark && NODE(curr).link == succ && NODE(succ).gen == s_gen -> goto finish;
            :: else -> printf("marking failed for remove of %d\n", value); goto retry;
        fi;
    }
    atomic {
        GOTO_ON_FAIL(NODE(succ).gen == s_gen, retry);
        GOTO_ON_FAIL(NODE(pred).gen == p_gen, retry);
        GOTO_ON_FAIL(NODE(curr).gen == c_gen, retry);
        GOTO_ON_FAIL(!NODE(pred).mark, retry);
        if  :: NODE(pred).link == curr -> NODE(pred).link = succ;
            :: else -> goto finish;
        fi;

        DESTROY_NODE(curr);
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
                /* printf("checking node %d, next is %d\n", cur, NODE(cur).link); */
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


