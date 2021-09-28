#!/bin/bash

TIMEOUT="${1}"
FMLA="${2}"
LOG="${3}"

python3 /home/hydra/reelay-codegen/reelay.py "${FMLA}" > /dev/null 2>> error.log
python3 reelay.py "${FMLA}" "${LOG}" > /dev/null 2>> error.log
g++ -o monitor -O2 -pthread -I/home/hydra/reelay-codegen/cpp -I/home/hydra/reelay-codegen/examples/csv_monitor main.cpp
./run "${TIMEOUT}" ./monitor
rm -f Monitorrand.hpp main.cpp monitor
