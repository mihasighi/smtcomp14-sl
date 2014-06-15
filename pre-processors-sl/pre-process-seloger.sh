#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -slp ${FILE} &> /dev/null
rm ${FILE}
cat ${FILE}.slp

