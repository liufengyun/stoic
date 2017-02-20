############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# COQBIN=/var/tmp/coq-8.3pl2/bin/
#

# Default paths are as follows:

COQBIN=
TLC=./lib/tlc/src/

-include settings.sh


############################################################################

INCLUDES=-R $(TLC) TLC

COQC=$(COQBIN)coqc $(INCLUDES)
COQDOC=$(COQBIN)coqdoc --quiet --utf8 --html

############################################################################
# STABLE DEVELOPMENTS

############################################################################

ALL_SRC=$(wildcard *.v)
TLC_SRC=$(wildcard $(TLC)/*.v)

.PHONY: all lib clean
.SUFFIXES: .v .vo

all: $(ALL_SRC:.v:=.vo)
	$(COQC) $^

lib:
	make -C $(TLC)

libclean:
	make -C $(TLC) clean

.v.vo :
	$(COQC) $<

#######################################################

clean :
	rm -f *.vo *.dot *.glob

############################################################################
#
#coqdoc :
#	@mkdir -p doc_light
#	$(COQDOC) --gallina -d doc_light $(VFILES)
#
