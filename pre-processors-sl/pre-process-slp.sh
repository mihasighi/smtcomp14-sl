#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -slp ${FILE}
rm ${FILE}
cat ${FILE}.slp
rm ${FILE}.slp

