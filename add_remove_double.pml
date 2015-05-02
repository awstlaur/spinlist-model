#include "spinlist.pml"

init {
    run init_nodes();

    WAIT_FOR_INITIALIZATION();

    // B/C of the way the scheduler works this will check at all points possible.
    run check_sorted();
    run insert_sorted(0);
    run insert_sorted(1);
    int i;
    select(i : 0 .. 1);
    run remove_sorted(i);
    run remove_sorted(i);
    printf("removing %d\n", i);
    /* run insert_sorted(3); */
}
