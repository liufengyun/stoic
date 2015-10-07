############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# COQBIN=/var/tmp/coq-8.3pl2/bin/
#

# Default paths are as follows:

COQBIN=
TLC=./lib/tlc/src/
SF=./lib/sf/

-include settings.sh


############################################################################

INCLUDES=-R $(TLC) TLC -R $(SF) SF

COQC=$(COQBIN)coqc $(INCLUDES)
COQDOC=$(COQBIN)coqdoc --quiet --utf8 --html

############################################################################
# STABLE DEVELOPMENTS

FILES=\
	stlc_cfun \
	stlc_cfun_ln \
	f_cfun_ln
	f_cfun_ln_v2

ALL=$(FILES)

############################################################################

ALL_SRC=$(ALL:=.v)
TLC_SRC=$(wildcard $(TLC)/*.v)
SF_SRC=$(wildcard $(SF)/*.v)

.PHONY: all lib clean
.SUFFIXES: .v .vo

all: $(ALL:=.vo)

lib:
	$(COQC) lib/sf/SfLib.v
	make -C $(TLC)

libclean:
	rm -f $(SF)*.vo $(SF)*.glob $(SF)*.v.d
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
