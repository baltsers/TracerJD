#!/bin/bash
ver=v0
seed=s1-orig
NT=${1:-"10"}

source ./schedule_global.sh

INDIR=$subjectloc/bin/$ver$seed

MAINCP=".:libs/polyglot.jar:libs/sootclasses-2.3.0.jar:libs/jasminclasses-2.3.0.jar:libs/java_cup.jar:libs/LocalsBox.jar:$subjectloc/lib:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar:$INDIR"

OUTDIR=$subjectloc/Runout-${ver}${seed}-uninstr
mkdir -p $OUTDIR

function RunOneByOne()
{
	# to run a single test at a time
	local i=0
	prefix="\/home\/hcai\/SVNRepos\/star-lab\/trunk\/Subjects\/Schedule1"
	sed s'/\\/\//g' $subjectloc/inputs/testinputs.txt > $subjectloc/inputs/testinputs.mod

	cat $subjectloc/inputs/testinputs.mod | dos2unix | \
	while read testname;
	do
		let i=i+1

		echo
		echo "Run Test #$i....."
		args=`echo $testname | sed s"/\.\./$prefix/"`
		echo $args
		java -Xmx4000m -ea -cp $MAINCP ScheduleClass $args \
		1> $OUTDIR/$i.out 2> $OUTDIR/$i.err
	done
}

function RunAllInOne()
{
	TMPDIR=$subjectloc/tracerInstrumented-$ver$seed
	mkdir -p $TMPDIR
	cp -fr $INDIR/* $TMPDIR/

	MAINCP="$MAINCP:$TMPDIR"
	java -Xmx1600m -ea -cp ${MAINCP} trace.Runner \
		"$subjectloc" \
		${ver}${seed} \
		$DRIVERCLASS \
		$NT \
		-nocaching

	rm -rf $OUTDIR
	mv $subjectloc/tracerOutdyn-${ver}${seed} $OUTDIR
	rm -rf $TMPDIR
}

starttime=`date +%s%N | cut -b1-13`
#RunOneByOne
RunAllInOne
stoptime=`date +%s%N | cut -b1-13`
echo "Normal RunTime for ${ver}${seed} elapsed: " `expr $stoptime - $starttime` milliseconds

exit 0


