#!/bin/bash

# This script acts as an unified running interface of your planner (all planners will have similar
# script). During the competition this script will be used by our infrastructure to run your
# planner. In this testing environment, the run.sh script in your team's home dir calls this plan.sh
# to demonstrate running of your planner.
#
# parameters:   plan.sh <domain-name> <problem-name>
# example:    ./plan.sh logistics00   probLOGISTICS-5-0
#
# <domain-name>: name of the domain the planner should be run for; one of the dirs in team's home
#     benchmarks/factored/ or benchmarks/unfactored (your planner can use the factored, unfactored
#     or both input files)
#
# <problem-name>: name of the problem in the domain <domain-name> the planner should solve; one of
#     the dirs in team's home benchmarks/factored/<domain-name>/ or
#     benchmarks/unfactored/<domain-name>/ (your planner can use the factored, unfactored or both
#     input files)
#
# <output-file>: file the planner should write the resuting plan in
#
# Note: If your planner needs to run some other service(s) before, this is the right place to do it
# (e.g., message brokers, etc.). The running time is computed including this script.


# *************** REPLACE BY CODE RUNNING YOUR PLANNER ***************
#rm out/domain.pddl
#rm out/problem.pddl
#./ma-to-pddl.py ../benchmarks/unfactored/$1/$2 domain problem out
#echo "" > results.txt
for d in "Test Domains"/*/ ; do
    DOMDIR="$d"domains/
    DOMAIN="$d"domain.pddl
    for f in  3 5 7 10 14 16 18 20 ; do
        PROBLEM="$d"instances/instance-"$f".pddl
        if [ -d "$DOMDIR" ]; then
            DOMAIN="$DOMDIR"domain-"$f".pddl
        fi
	FOUND="Valid Timed Plan found!"	
	OUT=$(timeout 30m ./gccRelease/tsat.exe "-y" "timing.dat" "-m" "1" "-t+" "3" "-limit" "14400" "-stagelimit" "1200" "$DOMAIN" "$PROBLEM" "solution.dat")
	#echo "$OUT"
	v=${d::-1}
	FINAL=$(basename "$v"),$f
#	echo "$FINAL"
	if echo "$OUT" | grep -q "$FOUND"; then
	    [[ $OUT =~ (Time: [0-9]*.[0-9]*) ]] && FINAL=$FINAL,"${BASH_REMATCH[1]//[^0-9.]}"
	else
	    FINAL=$FINAL,-1
	fi    
	echo "$FINAL" >> results.txt
	echo "$FINAL"

    done
done


#./fast-downward.py out/domain.pddl out/problem.pddl --search 'astar(lmcut())'
#cp sas_plan ../plan.out
#./mockup-planner ../benchmarks/unfactored/$1/$2/domain.pddl ../benchmarks/unfactored/$1/$2/problem.pddl ../plan.outSOURCE = "Solution found!"



