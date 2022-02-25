#!/bin/bash

cd "$(dirname "${0}")"

cd evaluation
./gen_log logs/shared 40000 4 4 0 16

for SIZE in 1 2 3 4 8 16; do
  for MAXR in 0 1 2 4 8; do
    for TYPE in 0 3; do
      for SEED in {0..3}; do
        ./test_single.sh "${SIZE}" "${MAXR}" "${TYPE}" "${SEED}"
       done
     done
   done
done
