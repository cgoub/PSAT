#ifndef Sat
#define Sat
#include <set>
#include <vector>

using namespace std;

//////////////////////////////////////////////////////////////////////
// Variables
struct var_t{
  int num;
} ;

var_t var(int num);

//////////////////////////////////////////////////////////////////////
// Littéraux
typedef unsigned int lit_t;

/** 
    Renvoie un littéral correspondant à la variable. Si positif est
    vrai, renvoie le littéral positif, sinon, renvoie le littéral
    négatif.
*/
lit_t var2lit(var_t v, bool positif);

/**
   Renvoie la variable correspondant à un littéral.
*/
var_t lit2var(lit_t l);

/**
   Renvoie vrai si le littéral est positif
*/
bool positif(lit_t l);

/**
   Renvoie le littéral opposé à un littéral donné.
*/
lit_t oppose(lit_t l);

//////////////////////////////////////////////////////////////////////
// Clauses
struct cls_t {
  set<lit_t> litteraux;
} ;

cls_t clause(const set<lit_t> & litteraux);
void ajouteLitteral(lit_t l, cls_t & cls);

//////////////////////////////////////////////////////////////////////
// Formules conjonctives
struct cnf_t {
  vector<cls_t> clauses;
} ;

cnf_t cnf(const vector<cls_t> & clauses);
void ajouteClause(const cls_t & clause, cnf_t & cnf);

//////////////////////////////////////////////////////////////////////
// Exploration de l'espace de recherche
enum val_t { vrai, faux, indeterminee };

struct etat_t {
  vector<val_t> valeurs;
  var_t derniere_affectee;
};

struct infos_retour_arriere_t {
  var_t variable_precedement_affectee;
  lit_t litteral_affecte;
};

/**
   Initialise la structure permettant d'explorer l'espace de recherche
   en utilisant nb_var variables.
*/
void init_etat(etat_t& etat, int nb_vars);

/**
   Donne la valeur d'un littéral en fonction des valeurs de variables.
*/
val_t valeur(const etat_t & etat, lit_t lit);

/**
   Evalue une clause en fonction des valeurs de variables.
 */
val_t evaluer_clause(const etat_t & etat, const cls_t & cls);

/**
   Evalue une formule conjonctive en fonction des valeurs de variables.
 */
val_t evaluer_cnf(const etat_t & etat, const cnf_t & cls);

/**
   Change la valeur de la variable correspondant au littéral. Si le
   littéral est positif, la variable aura la valeur vrai, s'il est
   négatif, elle aura la valeur faux.
*/
infos_retour_arriere_t affecte(etat_t & etat, cnf_t & cnf);

/**
   Rétablit l'état à sa valeur précédente en utilisant les informations contenues dans infos.
*/
void retour_arriere(etat_t & etat, cnf_t & cnf, const infos_retour_arriere_t & infos);

/**
   Choisit une variable et une valeur à affecter à cette variable.
   Renvoie un littéral positif si la variable doit être affectée à vrai, un littéral négatif sinon.
*/
lit_t choisit_litteral(const etat_t & etat, const cnf_t & cnf);

/**
   Cherche une affectation des variables telle que la formule conjonctive passée en argument s'évalue à vrai.
   L'état contient la valeur des variables déjà affectée (i.e. aucune variable au début de la recherche).
   Si la formule est satisfiable, la fonction renvoie true et l'état contient un modèle de la formule.
   Sinon la fonction renvoie false et l'état est identique à ce qu'il était avant la recherche (important pour les appels récursifs).
 */
bool cherche(etat_t & etat, cnf_t & cnf);

#endif

