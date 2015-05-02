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
                    ::  run check_sorted();
                    ::  select(i : F_LOW .. F_HIGH);
                        run search_sorted(i);
                    ::  len(node_gen) >= cnt - 1 ->
                            printf("adding node\n");
                            select(i : F_LOW .. F_HIGH);
                            cnt++;
                            run insert_sorted(i);
                    ::  //nfull(node_gen) ->
                            printf("removing node\n");
                            select(i : F_LOW .. F_HIGH);
                            run remove_sorted(i);
                fi
            fi
    od
}
