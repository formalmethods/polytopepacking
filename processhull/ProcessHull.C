#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>

using namespace std;

int main(int argc, char **argv) {

    if (argc != 2) {
        cerr << "Usage: " << argv[0] << " <input-file>" << endl;
        exit(-1);
    }

    vector<string> ors;

    fstream fin(argv[1], ios::in);

    unsigned hulls_n, poly_n, facets_n, v1, v2, cont;

    int coeff, p1, p2;
    char temp;

    fin >> poly_n;
    hulls_n = poly_n * (poly_n - 1) / 2;

    v1 = 1;
    v2 = 1;
    cont = 1;

    for (unsigned i=1; i <= hulls_n; i++) {

        if ( cont == poly_n ) { v1++; cont=v1; v2=v1; }

        cont++;
        v2++;

        fin >> p1; 
        fin >> p2; 
        fin >> facets_n;

        vector<string> disj_list;

        for ( unsigned j=1; j <= facets_n; j++ ) {

            // Coefficient of x

            fin >> coeff;

            bool second = false;

            stringstream lhs;
            lhs << "lhs_" << i << "_" << j;
            cout << "(define-fun " << lhs.str() << " () Real (+ ";

            if (coeff != 0) {
                cout << "(* " << -coeff << " p" << v1 << "x) (* " << coeff << " p" << v2 << "x) ";
                second = true;	
            }

            fin >> temp;  // skip the *
            fin >> temp;  // skip the variable
            fin >> temp;  // skip the +

            // Coefficient of y

            fin >> coeff;

            if (coeff != 0) {
                cout << "(* " << -coeff << " p" <<  v1 << "y) (* " << coeff << " p" << v2 << "y) ";
                second = true;
            }

            fin >> temp;  // skip the *
            fin >> temp;  // skip the variable
            fin >> temp;  // skip the +

            // Coefficient of z

            fin >> coeff;

            if (coeff != 0) {
                cout << "(* " << -coeff << " p" << v1 << "z) (* " << coeff << " p" << v2 << "z)";
            }

            fin >> temp;  // skip the *
            fin >> temp;  // skip the variable
            fin >> temp;  // skip the +

            cout << "))" << endl; // closes + and define-fun

            // Constant
            fin >> coeff;

            stringstream disj;
            disj << "disj_" << i << "_" << j;
            disj_list.push_back(disj.str());
            cout << "(define-fun " << disj.str() << " () Bool ";

            // Less than
            fin >> temp; 
            fin >> temp; 
            fin >> temp;

            cout << "(>= " << lhs.str() << " " << -coeff << "))" << endl;
        }

        cout << "(assert (or"; 
        for (unsigned j = 0; j < disj_list.size(); j++) {
            cout << " " << disj_list[j];
        }
        cout << "))" << endl; // closes implies
    }

    cout << "(check-sat)" << endl;
    cout << "(get-model)" << endl;

    fin.close();

    return 0;
}
