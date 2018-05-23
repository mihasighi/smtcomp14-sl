#!/bin/bash

# ./do-getinfo-bench.sh dir-bench prefix-file dir-new

BENCH=$1
FILES=`ls $BENCH/$2*.smt2`
DEST=../../slcomp18.git/bench/$3

for f in $FILES
do
  # take action on each file. $f store current file name
  echo "===== $f"
  FN=`basename $f`
  sed -e "2,12w $FN.info" $f &> /dev/null
  # move to destination
  mv $FN.info $DEST/$FN.info
  echo "====="
done
