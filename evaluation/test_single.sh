#!/bin/bash

SIZE="${1}"
MAXR="${2}"
TYPE="${3}"
SEED="${4}"
FID="${1}_${2}_${3}_${4}"
LOG="logs/shared"
APS="8"

#gen_fmla PREFIX SIZE MAXR TYPE SCALE SEED APS
./gen_fmla "fmlas/z_${FID}" "${SIZE}" "${MAXR}" "${TYPE}" "1" "${SEED}" "${APS}"

../hydra "fmlas/z_${FID}.mdl" "${LOG}.log" > "output/z_${FID}.hydra" 2>> error.log
if [ "${?}" -ne 0 ]
then
  cp "fmlas/z_${FID}.mdl" "bug_${FID}.mdl"
  exit 1
fi

../vydra "fmlas/z_${FID}.mdl" "${LOG}.log" > "output/z_${FID}.vydra" 2>> error.log
if [ "${?}" -ne 0 ]
then
  cp "fmlas/z_${FID}.mdl" "bug_${FID}.mdl"
  exit 1
fi

diff "output/z_${FID}.hydra" "output/z_${FID}.vydra"
if [ "${?}" -ne 0 ]
then
  cp "fmlas/z_${FID}.mdl" "bug_${FID}.mdl"
  exit 1
fi
