.PHONY: clean
clean:
	rm -f pan pan.* _spin_nvr.tmp *.trail

binary: pan.c
	gcc -o pan pan.c

.PHONY: run
run:
	./pan -E -a -n