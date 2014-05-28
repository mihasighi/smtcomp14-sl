#----Set TPTP_HOME if not already imported from environment
#TPTP_HOME = ...

JJPARSER = $(TPTP_HOME)/JJParser


CC = gcc
CFLAGS = -g -Wall -I$(JJPARSER) -D TPTP_HOME=\"$(TPTP_HOME)\"
LFLAGS = -lm

OBJS = $(JJPARSER)/ListStatistics.o $(JJPARSER)/List.o $(JJPARSER)/Examine.o $(JJPARSER)/Modify.o $(JJPARSER)/Tree.o $(JJPARSER)/TreeStatistics.o $(JJPARSER)/ParseTPTP.o $(JJPARSER)/ParseTSTP.o $(JJPARSER)/PrintTSTP.o $(JJPARSER)/Parsing.o $(JJPARSER)/Signature.o $(JJPARSER)/Tokenizer.o $(JJPARSER)/Utilities.o $(JJPARSER)/Compare.o $(JJPARSER)/Interpret.o $(JJPARSER)/PrintXML.o $(JJPARSER)/PrintSMT2.o $(JJPARSER)/PrintDFG.o $(JJPARSER)/PrintOtter.o $(JJPARSER)/PrintKIF.o $(JJPARSER)/PrintSUMO.o $(JJPARSER)/FileUtilities.o $(JJPARSER)/SystemOnTPTP.o

all: $(OBJS)

TestParsing: $(OBJS) TestParsing.o
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $(OBJS) TestParsing.o

DRSParsing: $(OBJS) DRSParsing.o
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $(OBJS) DRSParsing.o

Leak: $(OBJS) Leak.o
	$(CC) -o $@ $(OBJS) Leak.o

TPTP_to_SMTLIB: $(OBJS) TPTP_to_SMTLIB.o
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $(OBJS) TPTP_to_SMTLIB.o

TestTree: $(OBJS) TestTree.o
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $(OBJS) TestTree.o

.c.o:
	$(CC) $(CFLAGS) -c -o $*.o $*.c

clean:
	rm -f *.o TestParsing TestTree
