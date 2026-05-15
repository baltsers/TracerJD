#!/bin/bash
ver=v0
seed=s1-orig
source ./schedule_global.sh
NT=${1:-"5"}

INDIR=$subjectloc/tracerOutdyn-${ver}${seed}

MAINCP=".:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar:$subjectloc/lib"

starttime=`date +%s%N | cut -b1-13`
	#"main" \
java -Xmx10g -ea -cp ${MAINCP} apps.DynSlicer \
	"$INDIR" \
	$subjectloc/sc.txt \
	$NT \
	#-debug

stoptime=`date +%s%N | cut -b1-13`
echo "RunTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds

echo "Running finished."

exit 0


# hcai vim :set ts=4 tw=4 tws=4

