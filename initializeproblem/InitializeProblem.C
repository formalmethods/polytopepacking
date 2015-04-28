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

  cout << "VAR" << endl;
  for ( unsigned i=1; i <= polytopes_n; i++ ) {
    cout << "p" << i << "x, ";
    cout << "p" << i << "y, ";
    cout << "p" << i << "z, ";
  }

  cout << "dummy : REAL" << endl;
  cout << "DEFINE h : REAL := " << h << endl;

  // Boolean Variable Declaration
  
  cout << "VAR" << endl;
  for ( unsigned i=1; i <= (polytopes_n * (polytopes_n-1))/2; i++ ) {
    cout << "or" << i;
    if ( i != (polytopes_n * (polytopes_n-1))/2 )
      cout << ", ";
  }
  cout << " : BOOLEAN" << endl << endl;

  cout << "FORMULA" << endl;

  // Height declaration
  //cout << "h <= " << h << " and" << endl;
  //cout << "h >= " << h << " and" << endl;

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
    cout << "p" << i << "x" << " >= " << -min_x << " and" << endl; 
    cout << "p" << i << "y" << " >= " << -min_y << " and" << endl; 
    cout << "p" << i << "z" << " >= " << -min_z << " and" << endl; 

    // Upper bounds for the vectors
    cout << "p" << i << "x" << " <= " << x_width - max_x << " and" << endl; 
    cout << "p" << i << "y" << " <= " << y_width - max_y << " and" << endl; 
    cout << "p" << i << "z" << " <= h - " << max_z << " and" << endl;
  } 

  cout << "#" << endl;
  
  for ( unsigned i=1; i <= polytopes_n * (polytopes_n - 1)/2; i++ ) {
    cout << "or" << i;
    cout << " and ";
  }

  cout << endl << "#" << endl;
  
  fin.close();
}
