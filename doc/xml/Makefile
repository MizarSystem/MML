# Autometed creation of XML schemas and documentation
# from the ##RNC comments in kernel sources

TRANG	= trang
PERL 	= perl
XMLLINT	= xmllint


sources = $(shell ls ../kernel/*.pas)

schemas = Mizar article byexplanations constructors definientia fromexplanations notations \
          registrations schemes theorems identifyregistrations

rnc_schemas	= $(addsuffix .rnc,$(schemas)) 
rng_schemas	= $(addsuffix .rng,$(schemas)) 
xsd_schemas	= $(addsuffix .xsd,$(schemas)) 

all: $(rnc_schemas)  $(rng_schemas) $(xsd_schemas) doc

Mizar.rnc: $(sources)
	cat $(sources) | $(PERL) -e \
        'local $$/;$$_=<>; while(m/#[#]RNC:((.|[\n])*?)[*]\)/g) { print $$1}' |\
        $(PERL) -ne 's/\bel([A-Z])/$$1/g; s/\bat([A-Z]\w*)/lc($$1)/eg; print $$_'\
	>  Mizar.rnc

%.rng: %.rnc
	$(TRANG) $*.rnc $*.rng

%.xsd: %.rnc
	$(TRANG) $*.rnc $*.xsd

doc: Mizar.rng Mizar.xsd
	cd doc; make; cd ..;

# some versions of xmllint are buggy, the notations validation
# now fails for my version
check-iniprel: $(rng_schemas)
	for i in `ls ../mizfiles/*.dco`; do \
	  $(XMLLINT) --noout --relaxng constructors.rng $$i; done
	for i in `ls ../mizfiles/*.dno`; do \
	  $(XMLLINT) --noout --relaxng notations.rng $$i; done
	for i in `ls ../mizfiles/*.dcl`; do \
	  $(XMLLINT) --noout --relaxng registrations.rng $$i; done
	for i in `ls ../mizfiles/*.the`; do \
	  $(XMLLINT) --noout --relaxng theorems.rng $$i; done
	for i in `ls ../mizfiles/*.def`; do \
	  $(XMLLINT) --noout --relaxng definientia.rng $$i; done
	for i in `ls ../mizfiles/*.sch`; do \
	  $(XMLLINT) --noout --relaxng schemes.rng $$i; done
	for i in `ls ../mizfiles/*.did`; do \
	  $(XMLLINT) --noout --relaxng identifyregistrations.rng $$i; done	  

check-prel: $(rng_schemas)
	for i in `ls $(MIZFILES)/prel/*/*.dco`; do \
	  $(XMLLINT) --noout --relaxng constructors.rng $$i; done
	for i in `ls $(MIZFILES)/prel/*/*.dno`; do \
	  $(XMLLINT) --noout --relaxng notations.rng $$i; done
	for i in `ls $(MIZFILES)/prel/*/*.dcl`; do \
	  $(XMLLINT) --noout --relaxng registrations.rng $$i; done
	for i in `ls $(MIZFILES)/prel/*/*.the`; do \
	  $(XMLLINT) --noout --relaxng theorems.rng $$i; done
	for i in `ls $(MIZFILES)/prel/*/*.def`; do \
	  $(XMLLINT) --noout --relaxng definientia.rng $$i; done
	for i in `ls $(MIZFILES)/prel/*/*.sch`; do \
	  $(XMLLINT) --noout --relaxng schemes.rng $$i; done
	for i in `ls $(MIZFILES)/prel/*/*.did`; do \
	  $(XMLLINT) --noout --relaxng identifyregistrations.rng $$i; done
