#include "spinlist.pml"

init {
    run init_nodes();

    WAIT_FOR_INITIALIZATION();

    // B/C of the way the scheduler works this will check at all points possible.
    run check_sorted();
    run insert_sorted(0);
    run insert_sorted(1);
    if
        :: run insert_sorted(0);
        :: run insert_sorted(1);
    fi
}

ltl correctly_sorted {
    always ( !initialized || eventually (
        //!initialized ||
        NODE(head).link != tail                                             &&
        NODE(NODE(head).link).data == 0                                     &&
        NODE(NODE(head).link).link != tail                                  &&
        NODE(NODE(NODE(head).link).link).data == 1                          &&
        NODE(NODE(NODE(head).link).link).link == tail
    ))
}
