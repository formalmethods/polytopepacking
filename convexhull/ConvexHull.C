#include <CGAL/Homogeneous.h>
#include <CGAL/convex_hull_3.h>
#include <CGAL/Polyhedron_3.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <cassert>
#include <CGAL/gmpxx.h>

#define DEBUG 0
#define DEAD_CODE 0

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

class FacetEq {

    public:
        RT _a, _b, _c, _d;

        FacetEq(const RT &a, const RT &b, const RT &c, const RT &d) 
        { _a = a; _b = b; _c = c; _d = d; }

        bool operator==(const FacetEq &f) 
        { return ( f._a == _a && f._b == _b && f._c == _c && f._d == _d ); }

        std::ostream &print(std::ostream &out) { 
            out << _a << "*x + " << 
                _b << "*y + " << 
                _c << "*z + " << 
                _d << " <= 0 ";

            return out;
        }	

        friend std::ostream &operator<<(std::ostream &out, FacetEq &f) { return f.print(out); }
};

typedef std::vector<FacetEq>			  FacetEqSet;

// Input routines
void parse_file(char *, PolySet &);
// Output routines
void print_plane(Plane &, std::ostream &);
void print_points(PointSet &);
void collect_simplified_planes(Plane &, FacetEqSet &, int); 
// Minkwski sum
void minkowski_diff(PointSet &, PointSet &, PointSet &);

int main(int argc, char **argv)
{
    // holds the list of points
    PointSet points;
    PolySet  polytopes;
    FacetEqSet faceteq;

    if (argc != 3) { 
        std::cerr << "Usage: " << argv[0] 
            << " <input_file> <simplification>" 
            << std::endl; 
        exit(-1);
    }

    int simplification = atoi(argv[2]);

    if ( simplification != 0 && simplification != 1 ) {
        std::cerr << "Error: simplification must be 0 or 1" << std::endl;
        exit(-1);
    }

    // Fill points with the points listed into the file
    parse_file(argv[1], polytopes);  

#if DEBUG
    // Prints the acquired points
    for ( PolySet::iterator i=polytopes.begin();
            i != polytopes.end();
            i++ ) {

        print_points(*i);
        std::cout << std::endl;
    }
#endif

    std::cout << polytopes.size() << std::endl;

    // compute convex hulls
    for ( unsigned i=0; i < polytopes.size()-1; i++) {

        for ( unsigned j=i+1; j < polytopes.size(); j++) {

            // define object to hold convex hull 
            // CGAL::Object resulting_polytope;
            Polyhedron resulting_polytope;

            PointSet diff;

            minkowski_diff(polytopes[i], polytopes[j], diff);

#if DEBUG
            print_points(diff);
#endif

            CGAL::convex_hull_3(diff.begin(), diff.end(), resulting_polytope);

#if DEAD_CODE
            Polyhedron polyhedron;
            Segment segment;
            Point point;

            if ( CGAL::assign (polyhedron, resulting_polytope) ) {
                std::cerr << "Convex hull is a polyhedron" << std::endl;
            } else if ( CGAL::assign (segment, resulting_polytope) ) {
                std::cerr << "Convex hull is a segment" << std::endl;
            } else if ( CGAL::assign (point, resulting_polytope) ) {
                std::cerr << "Convex hull is a point" << std::endl;
            } else {
                std::cerr << "An error occured" << std::endl;
                exit(-1);
            }
#endif
            faceteq.clear();

#if DEAD_CODE
            for ( Polyhedron::Facet_iterator k = polyhedron.facets_begin();
                    k != polyhedron.facets_end();
                    k++ ) {
#endif
                for ( Polyhedron::Facet_iterator k = resulting_polytope.facets_begin();
                        k != resulting_polytope.facets_end();
                        k++ ) {

                    Polyhedron::Facet::Halfedge_handle h = k->halfedge();

                    Plane plane(h->vertex()->point(), 
                            h->next()->vertex()->point(), 
                            h->next()->next()->vertex()->point());

                    collect_simplified_planes(plane, faceteq, simplification);
                }

                std::cout << i+1 << " " << j+1 << " " << faceteq.size() << std::endl;

                for ( FacetEqSet::iterator k = faceteq.begin();
                        k != faceteq.end();
                        k++ ) {
                    std::cout << *k << std::endl; 
                }
            }
        }

        std::cout << std::endl; 

        return 0;
    }

    void print_points(PointSet &points) {

        for ( PointSet::iterator i=points.begin();
                i != points.end();
                i++ ) {
            std::cout << i->x() << " " << i->y() << " " << i->z() << std::endl;
        }
    }

    void print_plane(Plane &p, std::ostream &out) {

        out << p.a() << "x + " 
            << p.b() << "y + " 
            << p.c() << "z + " 
            << p.d() << " <= 0"
            << std::endl;

    }

    void collect_simplified_planes(Plane &p, FacetEqSet &faceteq, int simplification) {

        CGAL::Gmpz a = p.a(), b = p.b(), c = p.c(), d = p.d(), gcd_res;

        if ( simplification ) {
            gcd_res = a;

            if ( gcd_res != 1 ) {
                gcd_res = CGAL::gcd(gcd_res, b);
                if ( gcd_res != 1 ) {
                    gcd_res = CGAL::gcd(gcd_res, c);
                    if ( gcd_res != 1 ) {
                        gcd_res = CGAL::gcd(gcd_res, d);
                    }
                }
            }

            a /= gcd_res; 
            b /= gcd_res;
            c /= gcd_res;
            d /= gcd_res;
        }

        FacetEq new_eq(a,b,c,d);
        bool found = false;

        for ( FacetEqSet::iterator i = faceteq.begin();
                i != faceteq.end() and !found;
                i++ ) {
            if ( (*i) == new_eq ) 
                found = true;
        }

        if ( !found ) 
            faceteq.push_back(new_eq);
    }

    void parse_file(char *filename, PolySet &polytopes) {

        assert(filename);
        assert(polytopes.empty());

        std::fstream fin(filename, std::ios::in);
        unsigned polytopes_n, vertex_n;
        int x, y, z;

        fin >> polytopes_n;

        for ( unsigned i=0; i < polytopes_n; i++ ) {

            fin >> vertex_n;

            PointSet points;

            for ( unsigned j=0; j < vertex_n; j++ ) {
                fin >> x;
                fin >> y;
                fin >> z;

                points.push_back(Point(x,y,z));
            }

            polytopes.push_back(points);
        } 

        fin.close();
    }

    void minkowski_diff(PointSet &p1, PointSet &p2, PointSet &diff) {

        for ( PointSet::iterator v1=p1.begin();
                v1 != p1.end();
                v1++ )
        {
            for ( PointSet::iterator v2=p2.begin();
                    v2 != p2.end();
                    v2++ )
            {

                CGAL::Vector_3<Kernel> tmp;
                tmp = *v1 - *v2;

                diff.push_back(Point(tmp.hx(), tmp.hy(), tmp.hz()));
            }
        }
    }
