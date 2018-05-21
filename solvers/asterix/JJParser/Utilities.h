#ifndef UTILITIES_H
#define UTILITIES_H
//-----------------------------------------------------------------------------
#define STRINGLENGTH 1024
#define SUPERSTRINGLENGTH 40960
#define MAX_STRING_PARTS 10240

typedef char String[STRINGLENGTH];
typedef char SuperString[SUPERSTRINGLENGTH];
typedef char * StringParts[MAX_STRING_PARTS];
//-----------------------------------------------------------------------------
void CodingError(char * ErrorMessage);

void ChangeStringIndex(int* Index,int Change);
void ExtendString(char ** ToExtend,char * ByThis, int * AllocatedLength);
void MakeBuffer(char ** Buffer,int * BufferSize);
void ExtendAndFree(char ** Buffer,char * WithThisToFree,int * BufferSize);
char * BufferReturn(char ** Buffer,char * UserBuffer);
void Free(void ** Memory);
void * Malloc(int Size);
void * Realloc(void * OldMemory,int Size);

char * CopyHeapString(char * String);
int MaximumOfInt(int I1,int I2);
double MaximumOfDouble(double D1,double D2);
void SeedRand(int Seed);
long RandomInRange(long Lowest,long Highest,int Seed);
int NameInList(char * Name,char * List);
int RemoveNameFromList(char * Name,char * List);
int Tokenize(char * BigString,StringParts SmallParts,char * Delimiters);

void PrintTimeStamp(char * Message);
//-----------------------------------------------------------------------------
#endif
