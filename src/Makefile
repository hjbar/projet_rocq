all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

fullclean:
	rm Makefile.coq
	rm Makefile.coq.conf

.PHONY: all clean
