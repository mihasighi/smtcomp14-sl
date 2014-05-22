(theory Slrd

 :smt-lib-version 2.0
 :written_by "Mihaela Sighireanu"
 :date "2012-07-10"
 :last_modified "2014-05-22"

 :sorts ((Field 2) (SetRef 1) (Space 0))

 :funs  ((emp Space)
         (ssep Space Space :left-assoc)
         (par (A) (pto A (SetRef A) Space :left-assoc))
         (tobool Space Bool)
         (tospace Bool Space)
         (par (A B) (ref (Field A B) B (SetRef A)))
         (par (A) (sref (SetRef A) (SetRef A) (SetRef A) :left-assoc))
         (loop Space)
        )

 :notes "The generic -- program independent -- signature for the SLRD logic."

 :definition
 "The SLRD theory corresponds to signature of the SLRD logic
  in which:
  - the sort Field denotes the set of reference fields defined in the program;
    a reference field is typed by two sorts, thus its arity is 2;
  - the sort SetRef denotes the set of typed location variables;
  - the sort Space denotes the set of spatial formulas;

  - for all sp in Space, v a location variable, sr in SetRef, 
             f in Field:
      - emp denotes the empty heap space constraint;

      - junk denotes the universal heap space constraint;

      - (ssep sp sp) denotes the strong separating space constraint;

      - (pto v sr) denotes the points-to space constraint from location v;

      - (toBool sp) transforms a space constraint into a boolean constraint;

      - (toSpace b) transforms a boolean formula into a space formula,
        mainly used to be able to type quantifiers in space formulas;

      - (ref f v) denotes the tuple used in a points-to constraint, where
        f is a reference field which value is v, type is a set;

      - (sref sr sr) denotes the union of sets of tuples used in the points-to
        constraint;

      - (loop sp) denotes the space formula represeting a loop and
        using the predicate called in sp;
 "

)
