#!/bin/bash
ver=v0
seed=s1-orig
source ./schedule_global.sh
NT=${1:-"5"}

INDIR=$subjectloc/tracerOutdyn-${ver}${seed}

MAINCP=".:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar"

SOOTCP=".:libs/rt.jar:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar:$subjectloc/lib:$subjectloc/bin/${ver}${seed}"

### static analysis

OUTDIR=$subjectloc/tracerInstrumented-$ver$seed-prof

function phase1() {
	mkdir -p $OUTDIR
	mkdir -p $subjectloc/out-TracerInstr-prof

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
		-stmtProf \
		-notracingval \
		-allowphantom \
		-staticCDInfo \
		-main-class ${DRIVERCLASS} -entry:${DRIVERCLASS} \
		-process-dir $subjectloc/bin/${ver}${seed}  \
		1>$subjectloc/out-TracerInstr-prof/instr-${ver}${seed}.out 2>$subjectloc/out-TracerInstr-prof/instr-${ver}${seed}.err
	stoptime=`date +%s%N | cut -b1-13`
	echo "StaticAnalysisTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds
}

### runtime tracing
MAINCP=".:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar:$subjectloc/lib:$OUTDIR"

function phase2() {
	starttime=`date +%s%N | cut -b1-13`
		#"-fullseq" 
	java -Xmx1600m -ea -cp ${MAINCP} trace.Runner \
		"$subjectloc" \
		${ver}${seed}-prof \
		$DRIVERCLASS \
		$NT \
		-stmtProf \
		5

	stoptime=`date +%s%N | cut -b1-13`
	echo "RunTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds
	#cp $OUTDIR/{varIds.out,staticCDInfo.dat,staticDDInfo.dat} $subjectloc/tracerOutdyn-${ver}${seed}-prof/
}

### trace analysis 

INDIR=$subjectloc/tracerOutdyn-${ver}${seed}-prof
function phase3() {
	starttime=`date +%s%N | cut -b1-13`
		#"main" \
	java -Xmx1g -ea -cp ${MAINCP} apps.StmtProf \
		"$INDIR" \
		$subjectloc/stmt.txt \
		$NT \
		-debug

	stoptime=`date +%s%N | cut -b1-13`
	echo "RunTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds
}

phase1
phase2
phase3

echo "All finished."

exit 0


# hcai vim :set ts=4 tw=4 tws=4

