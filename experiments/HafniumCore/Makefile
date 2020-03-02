COQMODULE    := HafniumCore
# COQTHEORIES  := $(wildcard */*.v) #*/*.v
COQTHEORIES  := $(shell find . -iname '*.v')
#https://stackoverflow.com/questions/4210042/how-to-exclude-a-directory-in-find-command
#COQTHEORIES  := $(shell find . -path ./extract -prune -o -iname '*.v')

.PHONY: all proof proof-quick graph

all:
	$(MAKE) proof
	$(MAKE) extract

extract: Makefile.coq $(COQTHEORIES) $(COQTHEORIES:.v=.vo)
	cd extract; ocamlbuild main.native
#	cd extract; ocamlbuild -clean && ocamlbuild main.native

graph:
		sh make_graph.sh

### Quick
# proof-quick: Makefile.coq $(COQTHEORIES)
# 	$(MAKE) -f Makefile.coq quick

proof-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQTHEORIES))

proof: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib $(COQMODULE)"; \
         echo "-R lang $(COQMODULE)"; \
         echo "-R hfc $(COQMODULE)"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean || true
	find . -name "*.vio" -type f -delete
	find . -name "*.v.d" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
	cd extract; ocamlbuild -clean
	git clean -Xf .
# $(MAKE) -f Makefile.coq-rsync clean || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf
