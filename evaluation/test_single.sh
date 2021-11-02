#!/bin/bash

SIZE="${1}"
MAXR="${2}"
SEED="${3}"
FID="${1}_${2}_${3}"
LOG="logs/shared"
APS="8"

#gen_fmla PREFIX SIZE MAXR TYPE SCALE SEED APS
./gen_fmla "fmlas/z_${FID}" "${SIZE}" "${MAXR}" "1" "1" "${SEED}" "${APS}"

echo "Testing $(cat fmlas/z_"${FID}".mdl)"

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

sed -i "/^[A-Z]/d" "output/z_${FID}.hydra"
diff "output/z_${FID}.hydra" "output/z_${FID}.vydra"
if [ "${?}" -ne 0 ]
then
  echo "DIFFERENT"
  cp "fmlas/z_${FID}.mdl" "bug_${FID}.mdl"
else
  echo "OK"
fi
