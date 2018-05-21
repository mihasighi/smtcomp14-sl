#ifndef MODIFY_H
#define MODIFY_H
//-----------------------------------------------------------------------------
#include "DataTypes.h"
#include "Utilities.h"
//-----------------------------------------------------------------------------
int SetName(ANNOTATEDFORMULA AnnotatedFormula,char * Name);
int SetSyntax(ANNOTATEDFORMULA AnnotatedFormula,SyntaxType Syntax);
int SetStatus(ANNOTATEDFORMULA AnnotatedFormula,StatusType Status,
StatusType SubStatus);
void UninterpretIntegersInSignature(SIGNATURE Signature);
void AritizeSymbolsInSignature(SIGNATURE Signature);
void DequoteSymbolsInSignature(SIGNATURE Signature);
void ExpandListAssumptions(LISTNODE Head,SIGNATURE Signature);
void DeDoubleNegateFormula(FORMULA * Formula);
int DeDoubleNegate(ANNOTATEDFORMULA AnnotatedFormula);
void NegateFormula(FORMULA * Formula);
int Negate(ANNOTATEDFORMULA AnnotatedFormula,int Simplify);
int NegateListOfAnnotatedTSTPNodes(LISTNODE Head,int Simplify);
void UniqueifyVariableNames(ANNOTATEDFORMULA AnnotatedFormula);
int RemoveVacuousQuantifiersFromAnnotatedFormula(
ANNOTATEDFORMULA AnnotatedFormula);
void QuantifyFormula(FORMULA * UnquantifiedFormula,
ConnectiveType Quantifier,VARIABLENODE VariableNode);
void Quantify(ANNOTATEDFORMULA AnnotatedFormula,ConnectiveType Quantifier);
void QuantifyList(LISTNODE Head,ConnectiveType Quantifier);
void FOFify(ANNOTATEDFORMULA AnnotatedFormula,ConnectiveType Quantifier);
void FOFifyList(LISTNODE Head,ConnectiveType Quantifier);
void RandomizeAnnotatedFormula(ANNOTATEDFORMULA AnnotatedFormula,
unsigned int Seed);
void EnsureShortForm(ANNOTATEDFORMULA AnnotatedFormula);
void DoUpdateRecordInList(TERM TheList,SIGNATURE Signature,
char * UsefulInformation,int DoRemove,int DoAdd);
int RemoveNamedTermFromList(char * Name,TERM TheList,int MaxToRemove);
int RemoveParentFromInferenceTerm(char * ParentName,TERM Source);
int SetSourceFromString(ANNOTATEDFORMULA AnnotatedFormula,SIGNATURE Signature,
char * StringSource);
void RemoveUsefulInformationFromAnnotatedFormula(
ANNOTATEDFORMULA AnnotatedFormula,SIGNATURE Signature,char * PrincipleSymbol);
void AddUsefulInformationToAnnotatedFormula(ANNOTATEDFORMULA AnnotatedFormula,
SIGNATURE Signature,char * UsefulInformation);
void UpdateUsefulInformationInAnnotatedFormula(ANNOTATEDFORMULA 
AnnotatedFormula,SIGNATURE Signature,char * UsefulInformation);
//-----------------------------------------------------------------------------
#endif
