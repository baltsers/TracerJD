#!/bin/bash
ver=v0
seed=s1-orig

source ./schedule_global.sh

mkdir -p $subjectloc/lib
javac -g:source -nowarn -d $subjectloc/lib -source 1.4 $subjectloc/src/${ver}${seed}/C_stdlib.java

mkdir -p $subjectloc/bin/${ver}${seed}
javac -cp $subjectloc/lib/:libs/DUAForensics.jar:libs/InstrReporters.jar:libs/deam.jar:libs/Sensa.jar:libs/mcia.jar:TracerJD.jar  \
	-g:source -nowarn \
	-source 1.4 \
	-d $subjectloc/bin/${ver}${seed} \
	$subjectloc/src/${ver}${seed}/ScheduleClass.java

# hcai vim :set ts=4 tw=4 tws=4

