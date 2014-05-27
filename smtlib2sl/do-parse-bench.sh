#!/bin/bash

# first argument
# BENCH decide the set of tests to be done
BENCH=$1
FILES=`ls $BENCH/$2*.smt2`

for f in $FILES
do
  # take action on each file. $f store current file name
  echo "===== $f"
  FN=`basename $f`
  ./compile -parse $f &> tmp/$FN.log
  tail -n 1 tmp/$FN.log
  echo "====="
done
