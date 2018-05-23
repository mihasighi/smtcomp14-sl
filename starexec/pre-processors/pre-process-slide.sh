#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -slide ${FILE} &> /dev/null
rm ${FILE}
cat ${FILE}.sld

