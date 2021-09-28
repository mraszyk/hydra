FILES = ../src/[^h]*.cpp
HEADERS = *.h ../src/*.h
CC = g++
CFLAGS = -std=c++17 -O3 -Wno-unused-result

all: test evaluation

test: $(FILES) $(HEADERS) gen_fmla gen_log

evaluation: $(FILES) $(HEADERS)	gen_fmla gen_log gen_mtl_fixed gen_mtl_exp gen_pcre run

gen_%: $(FILES) $(HEADERS) gen_%.cpp
	$(CC) $(CFLAGS) -I../src/ -o $@ $(FILES) $@.cpp

run: run.cpp
	$(CC) $(CFLAGS) -o $@ $@.cpp
