/*
 * Copyright (c) 2005 Roberto Bruttomesso
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy of 
 * this software and associated documentation files (the "Software"), to deal in 
 * the Software without restriction, including without limitation the rights to 
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies 
 * of the Software, and to permit persons to whom the Software is furnished to do 
 * so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all 
 * copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE 
 * SOFTWARE.
 */
#include <cstdlib>
#include <iostream>

using namespace std;

int main (int argc, char *argv[]) {

  if ( argc != 3 ) {
    cerr << "Usage: " << argv[0] << " <number-of-para> <max-size>" << endl;
    exit(1);
  }

  int p_number = atoi(argv[1]);
  int max_size = atoi(argv[2]);

  // Header
  cout << p_number << endl;
  
  for ( int i=0; i < p_number; i++ ) {

    int l = rand() % max_size + 1, 
	w = rand() % max_size + 1, 
	h = rand() % max_size + 1;
    
    // Polytope header
    cout << "8" << endl; 

    for ( int j=0; j < 8; j++ ) {
      cout << ((j/4)%2) * h << " " 
	   << ((j/2)%2) * w << " "
	   << (j%2) * l << endl;
    }
  }

  cout << endl;

  return 0;
}
