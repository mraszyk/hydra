FILES = *.cpp
HEADERS = *.h
CC = g++
CFLAGS = -std=c++17 -O3 -Wno-unused-result

hydra:	$(FILES) $(HEADERS) lexer.cpp parser.cpp
		$(CC) $(CFLAGS) -o $@ $(FILES)
		mv $@ ../hydra

lexer.cpp:	lexer.l
	flex lexer.l

parser.cpp:	parser.y lexer.cpp
	bison parser.y
