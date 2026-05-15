/* README for TracerJD, the trace-based dynamic dependence analysis framework and toolkit for Java */

1. Purpose
=======================
This short document provides the usage instruction of TracerJD with the example subject program enclosed.

2. Example
=======================
We use a small subject Schedule1 and its test suite, both obtained from the SIR repository
(http://sir.unl.edu/portal/index.php), as the example data to demonstrate the usage of TracerJD.

3. File list 
=======================
cleanup.sh 
	- for cleaning up all generated data
compile.sh 
	- for compile the subject program (and the library it needs) source code
dynSlicer.sh 
	- the backward dynamic slicer tool built on TracerJD (example client analysis of the tracing framework)
libs	
	- all libraries on which TracerJD depends 
README.txt 
	- this file
run_uninstr.sh 
	- run the original subject (i.e., without instrumentation)
schedule_global.sh 
	- environment variables, simply for better script organization
stmtCov.sh 
	- the statement coverage reporter built on TracerJD (example client analysis of the tracing framework)
stmtProf.sh 
	- the statement-level performance profiling tool built on TracerJD (example client analysis of the tracing framework)
subject 
	- content of the subject program Schedule1
TraceAnalysis.sh 
	- a set of unit tests of the tracing framework of TracerJD, focusing on testing the elementary dependence querying routines
TracerInstr.sh 
	-  the static analysis phase
TracerJD.jar 
	- the TracerJD toolkit
TracerRun.sh 
	- the runtime tracing phase

4. Usage
=======================
[** The compiled subject binary is included in the package, so you may just skip the first two steps **]
[** We have only tested this toolkit using JDK 1.6 **]

step 1: compile the subject 

	sh compile.sh

Optionally, you can run the original program to ensure the original code works in your environment, using

	sh run_uninstr.sh [number of inputs to run]

output will be in subject/Schedule1/Runout-v0s1-orig-uninstr

step 2: run the static analysis phase of TracerJD
	
	sh TracerInstr.sh 

Instrumented code, including auxiliary static data will be in subject/Schedule1/tracerInstrumented-v0s1-orig

step 3: run the runtime tracing phase to generate traces, one trace file per test input will be found in
subject/Schedule1/tracerOutdyn-v0s1-orig/

	sh TracerRun.sh [number of inputs to run]

step 4: optionally, you can run a quick test of the trace-analysis phase of TracerJD

	sh TraceAnalysis.sh [number of inputs use]

step 5. run the application tools built upon the TracerJD tracing framework framework
use
	sh dynSlicer.sh [number of inputs to use]
to obtain some backward slices of criterion listed in subject/Schedule1/sc.txt

use
	sh stmtCov.sh [number of inputs to use]
to obtain statement coverage of the first N input used (N is the number of inputs to use)

use 
	sh stmtProf.sh [number of inputs to use]
to obtain the statement execution time per test input; (the result will list the execution time in nanoseconds for each 
instance of the statement on each row

[ Commandline argument above ]
* The argument "[number of inputs to run/use]" indicating the size of the input set to run/use is optional 
(there are totally 2650 inputs available for this example subject), by default only 10 will be run/used for 
quick testing purpose.

[ Troubleshooting ]
If you cannot successfully go through the example usage steps, please do not hesitate to send an email to hcai@nd.edu.
Thanks for using this toolkit.

Haipeng Cai
11/2014
