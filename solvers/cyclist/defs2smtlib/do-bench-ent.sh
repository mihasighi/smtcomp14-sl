#!/bin/sh

# Execute
#  do-bench.sh <srcdir> <prefix-file> <root> <dst-dir>
#

CYCTOOL=slsat_check.native

SRCDIR=$1
BENCH=$2
ROOT=$3
DSTDIR=$4

for i in `ls ${SRCDIR}/${BENCH}*.defs`
do
	echo "---- Translate file \"${i}\" root ${ROOT}"
	cp ${i} tmp.defs
	# change identifiers used in SMTLIB2 as keywords
        sed -i 's/and/andg/g' tmp.defs
        sed -i 's/xor/xorg/g' tmp.defs
        sed -i 's/not/notg/g' tmp.defs
	${CYCTOOL} -r ${ROOT} -D tmp.defs
        FILE=`basename ${i}`
	FILE=${DSTDIR}/${FILE}.smt2
	cat set-info.ent.smt2 assert.smt2 info.smt2 &> ${FILE} 
	# replace primed variables by variables with suffix 00
	sed -i 's/\(.\)\x27/\100/g' ${FILE}
	echo "   into ${FILE}"
done


