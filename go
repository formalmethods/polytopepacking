#!/bin/bash

if [ $# -ne 4 ] 
then
    echo "Usage: ./go <input-file> <x-width> <y-width> <max-h>"
    exit
fi

prefix=$(basename $1)_${2}_${3}_${4}

echo "Creating the problem"
initializeproblem/initializeproblem $1 $2 $3 $4 > results/$prefix.smt2
echo "Computing the convex hulls ..."
convexhull/convexhull $1 1 > results/$prefix.hull
echo "Computing the non intersection constraints ..."
processhull/processhull results/$prefix.hull >> results/$prefix.smt2 
echo "Now solving ..."
time ../z3/build/z3 results/$prefix.smt2 > results/$prefix.model

grep "unsat" results/$prefix.model > /dev/null

if [ $? -eq 1 ]
then
    echo "Displaying the model"
    display/display $1 results/$prefix.model > results/$prefix.wrl
else
    echo "Problem was unsat"
fi
