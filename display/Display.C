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

#define DEBUG 0

#ifdef CGAL_USE_GMP
#include <CGAL/Gmpz.h>
typedef CGAL::Gmpz RT;
#else
#include <CGAL/MP_Float.h>
typedef CGAL::MP_Float RT;
#endif

typedef CGAL::Homogeneous<RT> Kernel;
typedef CGAL::Polyhedron_3<Kernel> Polyhedron;
typedef Kernel::Point_3 Point;
typedef Kernel::Plane_3 Plane;
typedef Kernel::Segment_3 Segment;
typedef std::vector<Point> PointSet;
typedef std::vector<PointSet> PolySet;

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

    pix << "p" << i << "x"; 
    piy << "p" << i << "y"; 
    piz << "p" << i << "z"; 
    
    for ( unsigned j=1; j <= vertex_n; j++ ) {

      fin >> x;
      fin >> y;
      fin >> z;

      pointset.push_back(Point((x + v2v[pix.str()]),
			                   (y + v2v[piy.str()]),
			                   (z + v2v[piz.str()]))); 

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
      exit(1);
    }
    
    CGAL::VRML_2_ostream out( std::cout );
    out << polyhedron;

  } 
  
  fin.close();

  return 0;
}

void parse_values(var2values &v2v, fstream &fin) {

  string token, var;
  double value;

  do {
    fin >> token;
    if (fin.eof()) {
        break;
    }

    if (token == "sat" ||
        token == "(model" ||
        token == "()" ||
        token == ")") {
        continue;
    }

    if (token == "unsat") {
        cout << "Problem was unsat" << endl;
        exit(1);
    }

    assert(token == "(define-fun");
    fin >> token;
    var = token;
    fin >> token;
    assert(token == "()");
    fin >> token;
    assert(token == "Real");
    char c; 
    fin >> c;
    if (c == '(') {
        fin >> token;
        assert(token == "(/");
        double num, den;
        fin >> num;
        fin >> den;
        value = num/den;
        fin >> c;
        assert(c == ')');
    } else {
        fin.putback(c);
        fin >> value;
    }
    fin >> token;
    assert(token == ")");
    v2v[var] = value; 
    assert(0);
    
  } while(!fin.eof());

#if DEBUG
  var2values::iterator it = v2v.begin();  
  for (; it != v2v.end(); it++) {
      cout << it->first << " -> " << it->second << endl;
  }
#endif
}
