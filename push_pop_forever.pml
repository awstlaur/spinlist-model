#include "spinlist.pml"

#define F_LOW -5
#define F_HIGH 5
init {
    run init_nodes();

    WAIT_FOR_INITIALIZATION();

    int i;
    int cnt;
    do
        :: select(cnt : 3 .. 12);
            printf("current node_gen: %d\n", len(node_gen));
            if :: _nr_pr < cnt ->
                if
                    ::  len(node_gen) >= (cnt - 1) ->
                            select( i : F_LOW .. F_HIGH );
                            printf("pushing %d\n", i);
                            cnt++;
                            run push(i);
                    ::  //nfull(node_gen) ->
                            printf("popping\n");
                            run pop();
                fi
            fi
    od
}
