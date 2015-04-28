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
