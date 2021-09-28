#!/bin/bash

TIMEOUT="${1}"
FMLA="${2}"
LOG="${3}"

cp "${FMLA}" /home/hydra/r2u2/w.mltl
cp "${LOG}" /home/hydra/r2u2/w.r2u2
cd /home/hydra/r2u2
BOUND="$(cat w.mltl | sed "s/.*\[\(.*\),.*\].*/\1/")"
BOUND="$(("${BOUND}" / 2 + 1))"
sed -i "s/#define L_DOT_BUFFER .*/#define L_DOT_BUFFER ${BOUND}/" src/R2U2Config.h
make clean >> error.log
make >> error.log
python3 r2u2prep.py w.mltl >> error.log
/home/hydra/evaluation/run "${TIMEOUT}" ./bin/r2u2 ./tools/binary_files w.r2u2
#cat R2U2.log | sed "s/^.*\(.\)/\1/g" | sed "s/T/true/g" | sed "s/F/false/g" >> error.log
