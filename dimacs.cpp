#include "dimacs.hpp"
#include <string>
#include <sstream>
#include <iostream>
lit_t fromDimacs(int d) {
  return (abs(d) - 1)*2 + (d < 0 ? 1 : 0);
}

int toDimacs(lit_t l) {
  return (l/2 +1) * ((l%2 == 0) ? 1 : -1);
}

void lit_ligne_dimacs(istream& input, set<lit_t> & lits, int & nbVars) {
  int n;
  do {
    input >> n;
    if (n != 0) {
      lits.insert(fromDimacs(n));
      nbVars = max(nbVars, abs(n));
    }
  } while(n != 0 && !input.eof());
}

void lit_dimacs(istream& input, dimacs & data) {
  string line;
  while (input.good() && !input.eof()) {
    getline(input,line);
    if (line.length() > 0 && line[0] != 'p' && line[0] != 'c') {
      istringstream buffer(line);
      set<lit_t> lits;
      lit_ligne_dimacs(buffer,lits,data.nbVars);
      cls_t cls = clause(lits);
      ajouteClause(cls, data.cnf);
    }
  }
}

set<lit_t> lit_sortie_sat(istream& input) {
  string line;
  set<lit_t> result;
  input >> line;
  if (line == "SAT") {
    int n;
    lit_ligne_dimacs(input, result, n);
  }
  return result;
}

void ecrit_ligne_dimacs(ostream& output, const set<lit_t> & lits) {
  for(auto it = lits.cbegin(); it != lits.cend(); ++it) {
    output << toDimacs(*it) << " ";
  }
  output << 0 << endl;
}

void ecrit_clause_dimacs(ostream& output, const cls_t& clause) {
  ecrit_ligne_dimacs(output, clause.litteraux);
}

void ecrit_sortie_sat(ostream& output, const set<lit_t> & litteraux_vrais, bool est_sat) {
  if (est_sat) {
    output << "SAT" << endl;
    ecrit_ligne_dimacs(output, litteraux_vrais);
  } else {
    output << "UNSAT" << endl;
  }
}
