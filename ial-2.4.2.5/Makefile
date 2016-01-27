ROOTS=  bool bool-test bool-thms bool-thms2 bool-kleene bool-to-string \
	braun-tree braun-tree-test \
        bst \
        combinators \
	char \
	datatypes \
        functions \
	eq \
        int \
	integer \
	io io-test io-test2 \
	level \
	list list-test list-thms list-thms2 list-merge-sort list-merge-sort-test \
	logic \
	maybe maybe-thms \
	nat nat-thms nat-division nat-division-wf nat-division-basic nat-to-string nat-tests nat-nonzero nat-log \
	neq \
	negation \
	product product-thms \
	runtime-only \
	string string-format \
	sum sum-thms \
	termination \
        tree tree-test \
	trie trie-thms \
	vector vector-test vector-sort \

SOURCES=$(ROOTS:=.agda)
DEPS=$(ROOTS:%=deps/%.deps)
TARGETS=$(ROOTS:=.agdai)

test-all: Makefile.deps $(TARGETS)

%.agdai : %.agda
	agda  -v 0 $<

Makefile.deps: $(DEPS)	
	@cat $(DEPS) > Makefile.deps

deps/%.deps : %.agda
	@mkdir -p deps
	@./find-deps.sh $< > $@

include Makefile.deps

clean:
	rm -f Makefile.deps $(TARGETS) $(DEPS)
