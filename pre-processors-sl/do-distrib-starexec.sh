#!/bin/sh

HDIR=`pwd`
ARCH=${HDIR}/sl-preprocessor
mkdir ${ARCH}
for i in cyclist slsat asterix seloger slide spen
do
	mkdir ${ARCH}/preprocess-${i}
	mkdir ${ARCH}/preprocess-${i}/bin
	cp pre-process-${i}.sh ${ARCH}/preprocess-${i}/process
	cp bin/compile ${ARCH}/preprocess-${i}/bin
        cd ${ARCH}
	tar cvf preprocess-${i}.tar preprocess-${i}/
	gzip preprocess-${i}.tar
        rm -rf preprocess-${i}
        cd ${HDIR}
done

tar cvf ${ARCH}.tar ${ARCH}/
gzip ${ARCH}.tar

