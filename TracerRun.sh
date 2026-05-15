#!/bin/bash
ver=v0
seed=s1-orig
NT=${1:-"5"}
source ./schedule_global.sh

INDIR=$subjectloc/tracerInstrumented-$ver$seed

MAINCP=".:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar:$subjectloc/lib:$INDIR"

starttime=`date +%s%N | cut -b1-13`

	#"-fullseq" 
java -Xmx9600m -ea -cp ${MAINCP} trace.Runner \
	"$subjectloc" \
	${ver}${seed} \
	$DRIVERCLASS \
	$NT \
	-caching

stoptime=`date +%s%N | cut -b1-13`
echo "RunTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds
cp $INDIR/{varIds.out,staticCDInfo.dat,staticDDInfo.dat,stmtids.out} $subjectloc/tracerOutdyn-${ver}${seed}/

echo "Running finished."

exit 0


# hcai vim :set ts=4 tw=4 tws=4

