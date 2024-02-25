#ifndef Dimacs
#define Dimacs
#include "sat.hpp"
#include <set>
#include <istream>

using namespace std;

struct dimacs {
  int nbVars;
  cnf_t cnf;
};

void lit_dimacs(istream& input, dimacs& data);
void ecrit_clause_dimacs(ostream& output, const cls_t& clause);

set<lit_t> lit_sortie_sat(istream& input);
void ecrit_sortie_sat(ostream& output, const set<lit_t> & litteraux_vrais, bool est_sat);

#endif
