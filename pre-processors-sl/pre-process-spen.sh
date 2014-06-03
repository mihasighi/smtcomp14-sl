#!/bin/sh

FILE=`basename $1`
cp $1 ${FILE}
./bin/compile -spen ${FILE}
rm ${FILE}
cat ${FILE}.spn

