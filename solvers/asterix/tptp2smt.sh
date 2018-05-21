#!/bin/bash

# first argument
# BENCH decide the set of tests to be done
BENCH=$1
FILES=`ls $BENCH/$2-*.tptp`

# third argument
# the destination directory
DST=$3

for f in $FILES
do
  # take action on each file. $f store current file name
  echo "===== $f"
  JJParser/TPTP_to_SMTLIB $f tmp.smt2
  cat set-info.smt2 tmp.smt2 &> $f.smt2 
  mv $f.smt2 $DST/.
  rm tmp.smt2
  echo "====="
done
