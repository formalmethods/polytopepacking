#!/bin/tcsh

if ( "$#" != 4 ) then
  echo "Usage: ./go <input-file> <x-width> <y-width> <max-h>"
  exit
endif

echo "Creating the problem"
./wrapper $1 $2 $3 $4 .problem.smt2

# echo "Solving the problem"
# Add new code

# echo "Displaying the model"
# display/display $1 .model > model.wrl

rm -f .model.temp
