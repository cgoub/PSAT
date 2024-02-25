#include "sat.hpp"

//////////////////////////////////////////////////////////////////////
// Variables
var_t var(int num) {
  var_t res;
  res.num = num;
  return res;
}

//////////////////////////////////////////////////////////////////////
// Littéraux


lit_t var2lit(var_t v, bool positif) {
  return positif ? 2 * v.num : 2 * v.num + 1;
}

var_t lit2var(lit_t l) {
  return var(l / 2);
}

bool positif(lit_t l) {
  return l % 2 == 0;
}
lit_t oppose(lit_t l) {
  return l % 2 == 0 ? l + 1 : l - 1;
}

//////////////////////////////////////////////////////////////////////
// Clauses
cls_t clause(const set<lit_t> & litteraux){
  cls_t res;
  res.litteraux = litteraux;
  return res;
}

void ajouteLitteral(lit_t l, cls_t & cls) {
  cls.litteraux.insert(l);
}

//////////////////////////////////////////////////////////////////////
// Formules conjonctives
cnf_t cnf(const vector<cls_t> & clauses){
  cnf_t res;
  res.clauses = clauses;
  return res;
}

void ajouteClause(const cls_t & clause, cnf_t & cnf) {
  cnf.clauses.push_back(clause);
}

/**
   Initialise la structure permettant d'explorer l'espace de recherche
   en utilisant nb_var variables.
*/
void init_etat(etat_t& etat, int nb_vars) {
    
    etat.valeurs.assign(nb_vars, indeterminee);
    etat.derniere_affectee.num = -1;
}

val_t valeur(const etat_t & etat, lit_t lit) {
    
    var_t var = lit2var(lit);
    
    if (positif(lit)) {
        return etat.valeurs[var.num - 1];
    } else {
         return etat.valeurs[var.num - 1] == vrai ? faux : vrai;
    }
}

val_t evaluer_clause(const etat_t & etat, const cls_t & cls) {
  for (lit_t lit : cls.litteraux) {
    if (valeur(etat, lit) == vrai) {
      return vrai;
    }
  }
  return faux;
}

/**
   Evalue une formule conjonctive en fonction des valeurs de variables.
 */
val_t evaluer_cnf(const etat_t & etat, const cnf_t & cnf) {
  for (const cls_t & cls : cnf.clauses) {
    if (evaluer_clause(etat, cls) == faux) {
      return faux;
    }
  }
  return vrai;
}

/**
   Change la valeur de la variable correspondant au littéral. Si le
   littéral est positif, la variable aura la valeur vrai, s'il est
   négatif, elle aura la valeur faux.
*/
infos_retour_arriere_t affecte(etat_t & etat, lit_t l) {
  val_t valeur_lit = positif(l) ? vrai : faux;
  var_t var = lit2var(l);
  etat.valeurs[var.num - 1] = valeur_lit;
  infos_retour_arriere_t infos;
  infos.variable_precedement_affectee = var;
  infos.litteral_affecte = l;
  return infos;
}

/**
   Rétablit l'état à sa valeur précédente en utilisant les informations contenues dans infos.
*/
void retour_arriere(etat_t & etat, cnf_t & cnf, const infos_retour_arriere_t & infos) {
  var_t var = infos.variable_precedement_affectee;
  lit_t lit = infos.litteral_affecte;
  etat.valeurs[var.num - 1] = indeterminee;
}

/**
   Choisit une variable et une valeur à affecter à cette variable.
   Renvoie un littéral positif si la variable doit être affectée à vrai, un littéral négatif sinon.
*/
lit_t choisit_litteral(const etat_t & etat, const cnf_t & cnf) {
  
  for (const cls_t & cls : cnf.clauses) {
    for (lit_t lit : cls.litteraux) {
      if (valeur(etat, lit) == indeterminee) {
        return lit;
      }
    }
  }
  
  return 1;
}


/**
   Cherche une affectation des variables telle que la formule conjonctive passée en argument s'évalue à vrai.
   L'état contient la valeur des variables déjà affectée (i.e. aucune variable au début de la recherche).
   Si la formule est satisfiable, la fonction renvoie true et l'état contient un modèle de la formule.
   Sinon la fonction renvoie false et l'état est identique à ce qu'il était avant la recherche (important pour les appels récursifs).
 */
bool chercher(etat_t &etat, cnf_t &cnf) {
   lit_t l = choisit_litteral(etat, cnf);
   infos_retour_arriere_t ret_arr = affecte(etat, cnf); 


    val_t val_cnf = evaluer_cnf(etat, cnf);

    if (val_cnf == vrai || (val_cnf == indeterminee && chercher(etat, cnf))) {
        return true;
    }

    retour_arriere(etat, cnf, ret_arr);

    l = oppose(l);
    ret_arr = affecte(etat, l);

    val_cnf = evaluer_cnf(etat, cnf);

    if (val_cnf == vrai || (val_cnf == indeterminee && chercher(etat, cnf))) {
        return true;
    } else {
        retour_arriere(etat, cnf, ret_arr);
        return false;
    }
}

