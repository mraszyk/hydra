FILES = *.cpp
HEADERS = *.h
CC = g++
CFLAGS = -std=c++17 -O3 -Wno-unused-result
OCAMLBUILD = ocamlbuild -ocamlopt "ocamlopt -O3 -unbox-closures -unbox-closures-factor 20 " -use-ocamlfind -use-menhir -package zarith -no-plugin -yaccflags --explain -lflags log.o

all: hydra vydra mdl2mdl

hydra: $(FILES) $(HEADERS) lexer.cpp parser.cpp
	$(CC) $(CFLAGS) -o $@ $(FILES)
	mv $@ ../hydra

lexer.cpp: lexer.l
	flex lexer.l

parser.cpp: parser.y lexer.cpp
	bison parser.y

mdl2mdl: mdl2mdl.ml verified.ml
	$(OCAMLBUILD) mdl2mdl.native
	cp mdl2mdl.native ../mdl2mdl

vydra: _build/log.o main.ml verified.ml
	$(OCAMLBUILD) main.native
	cp main.native ../vydra

_build/log.o: log.c
	ocamlc -c log.c
	mkdir -p _build
	mv log.o _build/log.o
