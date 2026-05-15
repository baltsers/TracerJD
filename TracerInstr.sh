#!/bin/bash
ver=v0
seed=s1-orig
source ./schedule_global.sh

MAINCP=".:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar"

mkdir -p $subjectloc/out-TracerInstr

#SOOTCP=.:/etc/alternatives/java_sdk/jre/lib/rt.jar:/etc/alternatives/java_sdk/jre/lib/jce.jar:
SOOTCP=".:libs/rt.jar:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar:$subjectloc/lib:$subjectloc/bin/${ver}${seed}"

OUTDIR=$subjectloc/tracerInstrumented-$ver$seed
mkdir -p $OUTDIR

starttime=`date +%s%N | cut -b1-13`
	#-debug \
	#-dumpJimple \
	#-wrapTryCatch \
   	#-duaverbose \
	#-dumpFunctionList \
	#-debug \
$JAVA -Xmx1600m -ea -cp ${MAINCP} profile.EventInstrumenter \
	-w -cp ${SOOTCP} \
	-p cg verbose:false,implicit-entry:false -p cg.spark verbose:false,on-fly-cg:true,rta:true \
	-f c -d "$OUTDIR" -brinstr:off -duainstr:off \
	-wrapTryCatch \
	-slicectxinsens \
	-notracingval \
	-allowphantom \
	-staticCDInfo \
	-main-class ${DRIVERCLASS} -entry:${DRIVERCLASS} \
	-process-dir $subjectloc/bin/${ver}${seed}  \
	1>$subjectloc/out-TracerInstr/instr-${ver}${seed}.out 2>$subjectloc/out-TracerInstr/instr-${ver}${seed}.err
stoptime=`date +%s%N | cut -b1-13`
echo "StaticAnalysisTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds

echo "Running finished."
exit 0


# hcai vim :set ts=4 tw=4 tws=4

