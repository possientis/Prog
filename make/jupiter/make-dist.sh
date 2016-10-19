#!/bin/sh

package=jupiter
version=1.0
tarname=${package}
distdir=${tarname}-${version}

mkdir -p ${distdir}/src
cp Makefile ${distdir}
cp src/Makefile ${distdir}/src
cp src/main.c ${distdir}/src

tar chf ${distdir}.tar ${distdir}
gzip ${distdir}.tar

rm -rf ${distdir}
