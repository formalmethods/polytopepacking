# Copyright (c) 2005 Roberto Bruttomesso
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of 
# this software and associated documentation files (the "Software"), to deal in 
# the Software without restriction, including without limitation the rights to 
# use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies 
# of the Software, and to permit persons to whom the Software is furnished to do 
# so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all 
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE 
# SOFTWARE.

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
