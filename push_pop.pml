#include "spinlist.pml"

init {
    run init_nodes();

    /* defines 'initialized' bool */
    WAIT_FOR_INITIALIZATION();

    run push(11);
    run push(11);
    run push(11);
    run pop();
    run pop();


}

ltl datum_exists {
    always ( eventually (
        NODE(NODE(head).link).data == 11
    ))
}