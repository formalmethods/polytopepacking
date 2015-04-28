#include <CGAL/Homogeneous.h>
#include <CGAL/convex_hull_3.h>
#include <CGAL/Polyhedron_3.h>
#include <CGAL/IO/Polyhedron_iostream.h>
#include <CGAL/IO/Polyhedron_VRML_2_ostream.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <sstream>
#include <CGAL/gmpxx.h>
#include <string>
#include <map>
#include <cstdlib>
#include <cstdio>
#include <cassert>

#define DEBUG 0

#ifdef CGAL_USE_GMP
#include <CGAL/Gmpz.h>
typedef CGAL::Gmpz RT;
#else
#include <CGAL/MP_Float.h>
typedef CGAL::MP_Float RT;
#endif

typedef CGAL::Homogeneous<RT>                     Kernel;
typedef CGAL::Polyhedron_3<Kernel>		  Polyhedron;
typedef Kernel::Point_3                           Point;
typedef Kernel::Plane_3				  Plane;
typedef Kernel::Segment_3			  Segment;
typedef std::vector<Point>			  PointSet;
typedef std::vector<PointSet>			  PolySet;

#define DEBUG 0

using namespace std;

typedef map<string, double> var2values;

void parse_values(var2values &, fstream &);

int main(int argc, char **argv) {

  if(argc != 3) {
    cerr << "Usage: " << argv[0] << " <polytopes-file> <model-file> " << endl;
    exit(-1);
  }

  fstream fin(argv[1], ios::in);
  fstream fmodel(argv[2], ios::in);

  PointSet pointset;
  var2values v2v;

  parse_values(v2v, fmodel);

  fmodel.close();
  
#if DEBUG
  for ( var2values::iterator i=v2v.begin();
	i!=v2v.end();
	i++ ) {
    cout << i->first << " = " << i->second << endl; 
  }
#endif

  unsigned polytopes_n, vertex_n;
  int x, y, z;
  
  fin >> polytopes_n;
  
  for ( unsigned i=1; i <= polytopes_n; i++ ) {

    fin >> vertex_n;
    pointset.clear();

    stringstream pix, piy, piz;

    pix << "p" << i << "x"; piy << "p" << i << "y"; piz << "p" << i << "z"; 
      
    
    for ( unsigned j=1; j <= vertex_n; j++ ) {

      fin >> x;
      fin >> y;
      fin >> z;

      pointset.push_back(Point((x + v2v[ pix.str() ]),
			       (y + v2v[ piy.str() ]),
			       (z + v2v[ piz.str() ]))); 

    }

    CGAL::Object resulting_polytope;

    CGAL::convex_hull_3(pointset.begin(), pointset.end(), resulting_polytope);

    Polyhedron polyhedron;
    Segment segment;
    Point point;

    if ( CGAL::assign (polyhedron, resulting_polytope) ) {
      //std::cerr << "Convex hull is a polyhedron" << std::endl;
    } else if ( CGAL::assign (segment, resulting_polytope) ) {
      //std::cerr << "Convex hull is a segment" << std::endl;
    } else if ( CGAL::assign (point, resulting_polytope) ) {
      //std::cerr << "Convex hull is a point" << std::endl;
    } else {
      std::cerr << "An error occured" << std::endl;
      exit(-1);
    }
    
    CGAL::VRML_2_ostream out( std::cout );
    out << polyhedron;

  } 
  
  fin.close();

  return 0;
}

void parse_values(var2values &v2v, fstream &fin) {

  string token, var;
  const string delim = "#";
  double value;

  do {
    
    // Get the variable or #
    fin >> token;

    if ( token == delim )
      continue;

    var = token;
    // Get the =
    fin >> token;
    // Get the value
    fin >> value;
    // Store the value   
    v2v[ var ] = value; 
    
  } while(token != delim);
}
