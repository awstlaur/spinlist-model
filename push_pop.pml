#include "spinlist.pml"

init {
    run init_nodes();

    /* defines 'initialized' bool */
    WAIT_FOR_INITIALIZATION();

    run push(11);

}

/*active proctype monitor(){
    atomic{
        NODE(head).link == NIL -> assert(false)
    }
}*/

ltl datum_exists {
    always ( eventually (
        NODE(NODE(head).link).data == 11
    ))
}