#!/bin/bash

cd "$(dirname "${0}")"
cd evaluation/

echo "Running experiments"

python3 run.py "${1}"
chmod +x run.sh
./run.sh

echo "Processing results"

python3 proc.py "${1}"

echo "Finished"
