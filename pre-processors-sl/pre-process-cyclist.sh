#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -cyclist ${FILE}
rm ${FILE}
cat ${FILE}.defs
rm ${FILE}.defs

