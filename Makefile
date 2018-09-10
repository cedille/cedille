IAL=~/ial

AGDA=agda
#AGDA=/home/astump/agda-2.5.1.2/.cabal-sandbox/bin/agda

SRCDIR=src

AUTOGEN = \
	cedille.agda \
	cedille-types.agda \
	cedille-main.agda \
        options.agda \
	options-types.agda \
	options-main.agda \
        cws.agda \
	cws-types.agda \
	cws-main.agda \
	templates.agda

AGDASRC = \
	to-string.agda \
	constants.agda \
	spans.agda \
	conversion.agda \
	syntax-util.agda \
	ctxt-types.agda \
	rename.agda \
	classify.agda \
	subst.agda \
	is-free.agda \
	lift.agda \
	rewriting.agda \
	ctxt.agda \
	main.agda \
	toplevel-state.agda \
	process-cmd.agda \
	general-util.agda \
	interactive-cmds.agda \
	untyped-spans.agda \
	rkt.agda \
	meta-vars.agda \
	cedille-options.agda \
	elaboration.agda \
	elaboration-helpers.agda \
	monad-instances.agda

CEDILLE_ELISP = \
		cedille-mode.el \
		cedille-mode/cedille-mode-context.el \
		cedille-mode/cedille-mode-errors.el \
                cedille-mode/cedille-mode-faces.el \
		cedille-mode/cedille-mode-highlight.el \
                cedille-mode/cedille-mode-info.el \
		cedille-mode/cedille-mode-library.el \
		cedille-mode/cedille-mode-summary.el \
		cedille-mode/cedille-mode-normalize.el \
		cedille-mode/cedille-mode-scratch.el \
		cedille-mode/cedille-mode-beta-reduce.el

SE_MODE = \
	se-mode/se.el \
	se-mode/se-helpers.el \
	se-mode/se-highlight.el \
	se-mode/se-inf.el \
	se-mode/se-macros.el \
	se-mode/se-mode.el \
	se-mode/se-navi.el \
	se-mode/se-pin.el \
	se-mode/se-markup.el

ELISP=$(SE_MODE) $(CEDILLE_ELISP)

TEMPLATESDIR = $(SRCDIR)/templates
TEMPLATES = $(TEMPLATESDIR)/Mendler.ced $(TEMPLATESDIR)/MendlerSimple.ced

FILES = $(AUTOGEN) $(AGDASRC)

SRC = $(FILES:%=$(SRCDIR)//%)
OBJ = $(SRC:%.agda=%.agdai)

LIB = --library-file=libraries --library=ial --library=cedille

all: cedille # elisp

libraries: 
	./create-libraries.sh

./src/CedilleParser.hs: parser/src/CedilleParser.y ./src/CedilleLexer.hs
	cd parser; make cedille-parser

./src/CedilleLexer.hs: parser/src/CedilleLexer.x
	cd parser; make cedille-lexer

./src/CedilleCommentsLexer.hs: parser/src/CedilleCommentsLexer.x
	cd parser; make cedille-comments-lexer

./src/CedilleOptionsParser.hs: parser/src/CedilleOptionsParser.y 
	cd parser; make cedille-options-parser

./src/CedilleOptionsLexer.hs: parser/src/CedilleOptionsLexer.x
	cd parser; make cedille-options-lexer

./src/templates.agda: $(TEMPLATES) $(TEMPLATESDIR)/TemplatesCompiler
	$(TEMPLATESDIR)/TemplatesCompiler

cedille:	$(SRC) Makefile libraries ./src/templates.agda ./src/CedilleParser.hs ./src/CedilleLexer.hs ./src/CedilleCommentsLexer.hs ./src/CedilleOptionsLexer.hs ./src/CedilleOptionsParser.hs
		$(AGDA) $(LIB) --ghc-flag=-rtsopts --ghc-flag=-optl-static --ghc-flag=-optl-pthread -c $(SRCDIR)/main.agda 
		mv $(SRCDIR)/main cedille

cedille-old:	$(SRC) Makefile libraries
		$(AGDA) $(LIB) --ghc-flag=-rtsopts -c $(SRCDIR)/main-old.agda 
		mv $(SRCDIR)/main-old cedille

# compilation of elisp not working
#
#elisp: $(SE_MODE:%.el=%.elc) $(ELISP:%.el=%.elc)
#
#%.elc: %.el
#	emacs --batch -L se-mode -L cedille-mode -f batch-byte-compile $<

cedille-prof:	$(SRC) Makefile
		$(AGDA) $(LIB) --ghc-flag=-rtsopts --ghc-flag=-prof --ghc-flag=-fprof-auto -c $(SRCDIR)/main.agda 
		mv $(SRCDIR)/main cedille-prof

cedille-main: $(SRCDIR)/cedille-main.agda
	$(AGDA) $(LIB) --ghc-flag=-rtsopts -c $(SRCDIR)/cedille-main.agda 

options-main: $(SRCDIR)/options-main.agda
	$(AGDA) $(LIB) -c $(SRCDIR)/options-main.agda 

cws-main: $(SRCDIR)/cws-main.agda
	$(AGDA) $(LIB) -c $(SRCDIR)/cws-main.agda 

cedille-templates-compiler: $(TEMPLATESDIR)/TemplatesCompiler.hs
	cd $(TEMPLATESDIR); ghc --make -i../ TemplatesCompiler.hs

cedille-deb-pkg:
	mkdir -p ./cedille-deb-pkg/usr/bin/
	mkdir -p ./cedille-deb-pkg/usr/share/emacs/site-lisp/cedille-mode/
	mkdir -p ./cedille-deb-pkg/debian/
	cp -R ./cedille-mode/ ./cedille-mode.el ./se-mode/ ./cedille-deb-pkg/usr/share/emacs/site-lisp/cedille-mode/
	cp ./cedille ./cedille-deb-pkg/usr/bin/
	cp ./cedille-deb-control ./cedille-deb-pkg/debian/control

clean:
	rm -f cedille $(SRCDIR)/main $(OBJ); cd parser; make clean

#lines:
#	wc -l $(AGDASRC:%=$(SRCDIR)//%) $(GRAMMARS:%=$(SRCDIR)//%) $(CEDILLE_ELISP)

lines:
	wc -l $(AGDASRC:%=$(SRCDIR)//%) $(CEDILLE_ELISP)

elisp-lines:
	wc -l $(CEDILLE_ELISP)

agda-lines:
	wc -l $(AGDASRC:%=$(SRCDIR)//%)

