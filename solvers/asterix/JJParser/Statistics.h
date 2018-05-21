#ifndef STATISTICS_H
#define STATISTICS_H
//-----------------------------------------------------------------------------
#include "DataTypes.h"

typedef enum {
    nodes,
    thf_nodes,
    tff_nodes,
    fof_nodes,
    cnf_nodes,
    leaves,
//----For CNF problems
    count_horn_clauses,
    count_rr_clauses,

//----General
    unit_formulae,
    type_formulae,
    defn_formulae,
    sequent_formulae,
    atoms,
    equality_atoms,
    variable_atoms,
    literal_count,
    terms,
    count_variables,
    count_singletons,
    count_formula_depth,
    count_term_depth,
    count_nothing
} CountType;

typedef enum {
    depth,
    literals,
    term_depth,
    formula_depth,
    maximize_nothing
} MaximizeType;

//-----------------------------------------------------------------------------
#endif
