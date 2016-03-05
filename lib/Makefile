ROOTS = \
  bool bool-thms \
  eq \
  false \
  list list-thms \
  maybe \
  nat nat-thms \
  sigma \
  true \
  vector

SOURCES=$(ROOTS:=.ced)
TARGETS=$(ROOTS:=.cede)

all: $(TARGETS)

%.cede : %.ced 
	@cedille $< ; if ( grep error $@ > /dev/null ) ; then echo "$<: ERROR"; else echo "$<"; fi

clean: 
	@rm -f $(TARGETS)
