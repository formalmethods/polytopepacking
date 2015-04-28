#include <fstream>
#include <iostream>
#include <cstdlib>

using namespace std;

int main(int argc, char **argv) {

  if ( argc != 5 ) {
    cerr << "Usage: " << argv[0] << " <input-file> <x-width> <y-width> <max-h>" << endl;
    exit(-1);
  }

  fstream fin(argv[1], ios::in);

  int x_width = atoi(argv[2]), y_width = atoi(argv[3]);
  double h = atof(argv[4]);
  unsigned polytopes_n, vertex_n;
  int x, y, z;
  
  fin >> polytopes_n;

  // Real Variables Declaration

  for ( unsigned i=1; i <= polytopes_n; i++ ) {
    cout << "(declare-fun p" << i << "x () Real)" << endl;
    cout << "(declare-fun p" << i << "y () Real)" << endl;
    cout << "(declare-fun p" << i << "z () Real)" << endl;
  }

  cout << "(declare-fun dummy () Real)" << endl;
  cout << "(define-fun h () Real " << h << ".0)" << endl;

  for ( unsigned i=1; i <= polytopes_n; i++ ) {

    fin >> vertex_n;
    
    fin >> x;
    fin >> y;
    fin >> z;
      
    int max_x = x, min_x = x, max_y = y, min_y = y, max_z = z, min_z = z;
    
    for ( unsigned j=2; j <= vertex_n; j++ ) {

      fin >> x;
      fin >> y;
      fin >> z;

      if ( x < min_x ) min_x = x;
      if ( x > max_x ) max_x = x;
      if ( y < min_y ) min_y = y;
      if ( y > max_y ) max_y = y;
      if ( z < min_z ) min_z = z;
      if ( z > max_z ) max_z = z;
    }

    // Lower Bounds for the vectors 
    cout << "(assert (>= p" << i << "x" << " " << -min_x << "))" << endl; 
    cout << "(assert (>= p" << i << "y" << " " << -min_y << "))" << endl; 
    cout << "(assert (>= p" << i << "z" << " " << -min_z << "))" << endl; 

    // Upper bounds for the vectors
    cout << "(assert (<= p" << i << "x" << " " << x_width - max_x << "))" << endl; 
    cout << "(assert (<= p" << i << "y" << " " << y_width - max_y << "))" << endl; 
    cout << "(assert (<= p" << i << "z" << " (- h " << max_z << ")))" << endl;
  } 

  fin.close();
}
