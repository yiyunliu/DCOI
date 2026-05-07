COQMAKEFILE=CoqMakefile
COQDOCJS_DIR ?= coqdocjs
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

SYNTAX_FILES = theories/Autosubst2/syntax.v \
               theories/Autosubst2/core.v \
               theories/Autosubst2/unscoped.v

theories: $(COQMAKEFILE) FORCE
	$(MAKE) -f $(COQMAKEFILE)

coqdoc: $(COQMAKEFILE)
	$(MAKE) -f $^ html
	cp -R $(EXTRA_DIR)/resources html

validate: $(COQMAKEFILE) FORCE
	$(MAKE) -f $(COQMAKEFILE) validate

$(COQMAKEFILE) : $(SYNTAX_FILES)
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

# Regenerate the de-Bruijn syntax with autosubst-ocaml. We then post-process
# the generated syntax.v through gen_syntax.pl to wrap it in the
# `Module Type syntax_sig (Export lattice : Lattice).` functor that the
# proofs expect.
$(SYNTAX_FILES) : syntax.sig gen_syntax.pl
	autosubst -f -v ge813 -s urocq -o theories/Autosubst2/syntax.v syntax.sig
	perl gen_syntax.pl

.PHONY: clean FORCE deepclean coqdoc theories install uninstall validate

clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )

deepclean: clean
	rm -f theories/Autosubst2/syntax.v theories/Autosubst2/core.v theories/Autosubst2/unscoped.v

FORCE:
