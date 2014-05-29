COMPILE = ../compile -slide
SLIDE = ../slide-wrapper.sh

BENCH = dll-entails-dll-rev.smt2 dll-spaghetti.smt2 tll-entails-node-tll-tll.smt2 dll-entails-node-dll-rev.smt2	dll2-entails-dll2-rev.smt2 tll-pp-entails-tll-pp-rev.smt2 dll-entails-node-node-dll.smt2 dll2-rev-entails-dll2.smt2 tll-pp-rev-entails-tll-pp.smt2 dll-mid-entails-dll-rev.smt2	dll2-spaghetti-existential.smt2 tll-ravioli-existential.smt2 dll-rev-entails-dll-mid.smt2 node-dll-rev-dll-entails-dll.smt2  tll-ravioli.smt2 dll-rev-entails-dll.smt2 node-node-dll-entails-dll.smt2 tree-pp-entails-tree-pp-rev.smt2 dll-spaghetti-existential.smt2 node-tll-tll-entails-tll.smt2 tree-pp-rev-entails-tree-pp.smt2

all: 
	@(\
		for i in $(BENCH);	 				\
		do echo "TESTING $$i ...";				\
		$(COMPILE) $$i > /dev/null 2> /dev/null;		\
		$(SLIDE) $$i.sld; 					\
		done;							\
	)

clean: 
	rm -rf *.sld *~
