#include "spinlist.pml"

init {
    run init_nodes();

    /* defines 'initialized' bool */
    WAIT_FOR_INITIALIZATION();

    run push(21);
    run push(21);
    run pop();


}

ltl datum_exists {
    always ( eventually (
        NODE(NODE(head).link).data == 21
    ))
}