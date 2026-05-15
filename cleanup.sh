#!/bin/bash

source ./schedule_global.sh

rm -rf $subjectloc/{bin,lib}
rm -rf $subjectloc/Runout-*-uninstr
rm -rf $subjectloc/tracerInstrumented*
rm -rf $subjectloc/tracerOutdyn*
rm -rf $subjectloc/out-*

