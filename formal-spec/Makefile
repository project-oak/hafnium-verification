coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
