#!/bin/sh

HDIR=`pwd`
ARCH=${HDIR}/sl-preprocessor
mkdir ${ARCH}
for i in cyclist slsat seloger sleek slide spen
do
	mkdir ${ARCH}/preprocess-${i}
	mkdir ${ARCH}/preprocess-${i}/bin
	cp pre-process-${i}.sh ${ARCH}/preprocess-${i}/process
 	COMPILER=compile
	if [ ${i} == sleek ]; then
	  COMPILER=smt2slk
	fi
	cp bin/${COMPILER} ${ARCH}/preprocess-${i}/bin
        cd ${ARCH}/preprocess-${i}/
	tar czvf ../preprocess-${i}.tgz *
	cd ${ARCH}
        rm -rf preprocess-${i}
        cd ${HDIR}
done

tar czvf ${ARCH}.tgz ${ARCH}/

