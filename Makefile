include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.tz: %.vo util.vo
	./maketz $(basename $<) $@

%.ccg: %.vo util.vo
	./makeccg $(basename $<) $@
