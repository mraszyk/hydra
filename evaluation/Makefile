FILES = ../src/[^h]*.cpp
HEADERS = *.h ../src/*.h
CC = g++
CFLAGS = -std=c++17 -O3 -Wno-unused-result

all: test evaluation

test: gen_fmla gen_log

evaluation: gen_fmla gen_log gen_mdl_quad gen_mtl_exp gen_mtl_fixed run

gen_%: $(FILES) $(HEADERS) gen_%.cpp
	$(CC) $(CFLAGS) -I../src/ -o $@ $(FILES) $@.cpp

run: run.cpp
	$(CC) $(CFLAGS) -o $@ $@.cpp
