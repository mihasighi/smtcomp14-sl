#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -cyclist ${FILE} &> /dev/null
rm ${FILE}
cat ${FILE}.defs

