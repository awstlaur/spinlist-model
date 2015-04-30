#include "spinlist.pml"

init {
    run init_nodes();

    WAIT_FOR_INITIALIZATION();

    run insert_sorted(0);
    run insert_sorted(1);
    run insert_sorted(2);
    run insert_sorted(3);
}

/* ltl correctly_sorted { */
/*     eventually ( */
/*         initialized && */
/*         NODE(head).link != tail                                             && */
/*         NODE(NODE(head).link).data == 0                                     && */
/*         NODE(NODE(head).link).link != tail                                  && */
/*         NODE(NODE(NODE(head).link).link).data == 1                          && */
/*         NODE(NODE(NODE(head).link).link).link != tail                       && */
/*         NODE(NODE(NODE(NODE(head).link).link).link).data == 2               && */
/*         NODE(NODE(NODE(NODE(head).link).link).link).link != tail            && */
/*         NODE(NODE(NODE(NODE(NODE(head).link).link).link).link).data == 3 */   
/*         /1* NODE(NODE(NODE(NODE(NODE(head).link).link).link).link).link == tail *1/ */
/*     ) */
/* } */
