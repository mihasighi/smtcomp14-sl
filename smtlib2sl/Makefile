# Makefile
#


include ./Makefile.config

#---------------------------------------
# Flags
#---------------------------------------

# Use ICFLAGS to specify machine-independent compilation flags.
ICFLAGS = -g -I. -I$(SMTLIB2_PREFIX)

LDFLAGS = -L$(SMTLIB2_PREFIX) \

#DEBUG=_debug

#---------------------------------------
# Files
#---------------------------------------

CCINC = sl_vector.h sl_util.h \
	sl_type.h sl_var.h sl_pred.h sl_form.h sl_prob.h \
	sl.h smtlib2sl.h \
	sl_prob2cyclist.h sl_prob2sleek.h sl_prob2slp.h sl_prob2sl.h sl_prob2slide.h sl_prob2spen.h 

CCSRC = sl_util.c \
	sl_type.c sl_var.c sl_pred.c sl_form.c sl_prob.c \
	sl.c smtlib2sl.c \
	sl_prob2cyclist.c sl_prob2sleek.c  sl_prob2slp.c sl_prob2sl.c sl_prob2slide.c sl_prob2spen.c \
 	smtlib2sl_compile.c

#---------------------------------------
# Rules
#---------------------------------------

SHARED_LIBS = -lsmtlib2parser -lm

all: compile

compile: $(subst .c,$(DEBUG).o,$(CCSRC)) 
	$(CXX) $(CXXFLAGS) -o $@ $^ $(LDFLAGS) $(SHARED_LIBS)

clean:
	rm -f *.o *~ *.defs *.slp *.sle *.sld
	
distclean: clean
	rm smtlib2sl_compile

install: smtlib2sl_compile
	mv smtlib2sl_compile $(HOME)/bin

indent: $(CCINC) $(CCSRC)
	indent -nut $^

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so .cc

%.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $<

%_debug.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<


