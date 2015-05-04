#include "spinlist.pml"

init {
    run init_nodes();

    /* defines 'initialized' bool */
    WAIT_FOR_INITIALIZATION();

    run push(11);
   
}

ltl list_empty {
    always ( eventually (
        NODE(NODE(head).link).data == 11
    ))
}