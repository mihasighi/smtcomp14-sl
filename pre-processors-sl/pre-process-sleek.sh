#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/smt2slk ${FILE}
rm ${FILE}
cat ${FILE}.slk

