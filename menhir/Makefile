BASENAMES=$(patsubst %.mly,%,$(wildcard *.mly))
LR_AUTOMATA=$(patsubst %,%_lr.automaton,$(BASENAMES))
LR_MLIs=$(patsubst %,%_lr.mli,$(BASENAMES))
LR_MLs=$(patsubst %,%_lr.ml,$(BASENAMES))
LALR_AUTOMATA=$(patsubst %,%_lalr.automaton,$(BASENAMES))
LALR_MLIs=$(patsubst %,%_lalr.mli,$(BASENAMES))
LALR_MLs=$(patsubst %,%_lalr.ml,$(BASENAMES))

all: $(LR_AUTOMATA) $(LALR_AUTOMATA)

%_lr.automaton: %.mly
	@echo 'Building LR automaton for $* ($@)' 
	@menhir --dump --canonical $< --base $*_lr

%_lalr.automaton: %.mly
	@echo 'Building LALR automaton for $* ($@)' 
	@menhir --dump --lalr $< --base $*_lr

clean:
	rm -f $(LR_AUTOMATA) $(LR_MLIs) $(LR_MLs)
	rm -f $(LALR_AUTOMATA) $(LALR_MLIs) $(LALR_MLs)

.PHONY: all clean
