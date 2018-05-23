#!/bin/bash

# ./do-2sl18-bench.sh dir-bench prefix-file dir-new

BENCH=$1
FILES=`ls $BENCH/$2*.smt2`
DEST=../../slcomp18.git/bench/$3

for f in $FILES
do
  # take action on each file. $f store current file name
  echo "===== $f"
  FN=`basename $f`
  ./compile -sl18 $f &> tmp/$FN.log
  # output in $f.sl2
  ../../slcomp-parser.git/slcomp-parser $f.sl2 &> tmp/$FN.log
  tail -n 1 tmp/$FN.log
  # create new file with logic and info
  cat $DEST/logic.smt2 $DEST/$FN.info $f.sl2 &> $DEST/$FN
  # remove the .sl2 prefix
  #rm $f.sl2 
  echo "====="
done
