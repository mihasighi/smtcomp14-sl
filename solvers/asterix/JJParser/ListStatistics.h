#ifndef LISTSTATISTICS_H
#define LISTSTATISTICS_H
//-----------------------------------------------------------------------------
#include "DataTypes.h"
#include "Statistics.h"

typedef struct {
    double NumberOfFormulae;
    double NumberOfTHF;
    double NumberOfTFF;
    double NumberOfFOF;
    double NumberOfCNF;

    double NumberOfTypeFormulae;
    double NumberOfDefnFormulae;
    double NumberOfSequents;
    double NumberOfUnitFormulae;  //----Doubles as NumberOfUnitClauses;
    double NumberOfAtoms;  //----Doubles as NumberOfLiterals;
    double NumberOfEqualityAtoms;  //----Doubles as NumberOfEqualityLiterals
    double NumberOfVariableAtoms;
    double NumberOfLiterals;

    double NumberOfPredicates;  //----Doubles as number of symbols
    double NumberOfPropositions; 
    double MinPredicateArity;
    double MaxPredicateArity;
    double NumberOfFunctors;
    double NumberOfConstants;
    double MinFunctorArity;
    double MaxFunctorArity;
    double NumberOfVariables;
    double NumberOfSingletons;
    double MaxTermDepth;
    double AverageTermDepth;
    double NumberOfMathPredicates;
    double NumberOfMathFunctions;
    double NumberOfNumbers;

//----Only THF connectives
    double NumberOfPIs;
    double NumberOfSIGMAs;
    double NumberOfApplications;
    double NumberOfEquations;
    double NumberOfGlobalTypeDecs;
    double NumberOfGlobalDefns;
    double NumberOfTypeConnectives;
    double NumberOfMAPARROWs;
    double NumberOfXPRODs;
    double NumberOfUNIONs;
    double NumberOfLambdas;
    double NumberOfTypedVariables;
    double NumberOfDefinedVariables;
    double NumberOfPIVariables;
    double NumberOfSIGMAVariables;
    double NumberOfDescriptionVariables;
    double NumberOfChoiceVariables;

//----Only TFF
    double NumberOfSubtypes;

//----Not for CNF
    double MaxFormulaDepth;
    double AverageFormulaDepth;
    double NumberOfConnectives;
    double NumberOfNegations;
    double NumberOfDisjunctions;
    double NumberOfConjunctions;
    double NumberOfEquivalences;
    double NumberOfImplications;
    double NumberOfReverseImplications;
    double NumberOfXORs;
    double NumberOfNORs;
    double NumberOfNANDs;
    double NumberOfUniversals;
    double NumberOfExistentials;

//----Only for CNF
    double NumberOfHornClauses;
    double NumberOfRRClauses;
    double MaxClauseSize;
    double AverageClauseSize;

} ListStatisticsRecordType;
//-----------------------------------------------------------------------------
int ListCount(LISTNODE List,CountType WhatToCount);
int HeadListCount(HEADLIST HeadListHead,CountType WhatToCount);
int ListMaximal(LISTNODE List,MaximizeType WhatToMaximize);

void GetListSymbolUsageStatistics(HEADLIST HeadList,
double * NumberOfPredicates,double * NumberOfPropositions,
double * MinPredicateArity,double * MaxPredicateArity,
double * NumberOfFunctors,double * NumberOfConstants,
double * MinFunctorArity, double * MaxFunctorArity);
ListStatisticsRecordType * GetListStatistics(LISTNODE ListHead,
SIGNATURE Signature,ListStatisticsRecordType * Statistics);
void PrintListStatistics(FILE * Stream,ListStatisticsRecordType Statistics);
//-----------------------------------------------------------------------------
#endif
