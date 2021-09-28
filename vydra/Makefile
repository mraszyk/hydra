EXENAME=vydra
MODULENAME=main
NAME=$(MODULENAME)
OCAMLBUILD=ocamlbuild -ocamlopt "ocamlopt -O3 -unbox-closures -unbox-closures-factor 20 " -use-ocamlfind -use-menhir -package zarith -no-plugin -yaccflags --explain -lflags log.o
OCAMLFIND=ocamlfind

SOURCEFOLDER=.

standalone: _build/log.o
	$(OCAMLBUILD) $(NAME).native
	mv -f $(MODULENAME).native $(EXENAME).native
	mv $(EXENAME).native ../vydra.opt

_build/log.o: log.c
	ocamlc -c log.c
	mkdir -p _build
	mv log.o _build/log.o

clean:
	$(OCAMLBUILD) -clean
