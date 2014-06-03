#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -slide ${FILE}
rm ${FILE}
cat ${FILE}.sld

