#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/smt2slk ${FILE} &> /dev/null
rm ${FILE}
cat ${FILE}.slk

