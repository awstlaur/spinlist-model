#include "spinlist.pml"

init {
    run init_nodes();

    /* defines 'initialized' bool */
    WAIT_FOR_INITIALIZATION();

    run push(21);
    run append(22);
   /*run append(23);*/
    run pop();



}

ltl pushed_gets_popped {
    always ( eventually (
        NODE(NODE(head).link).data == 22 || NODE(NODE(head).link).data == 21
        /*|| NODE(NODE(head).link).data == 13*/
    ))
}