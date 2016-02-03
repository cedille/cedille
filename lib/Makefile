ROOTS = \
  bool bool-thms \
  false \
  list list-thms \
  nat nat-thms \
  true \
  vector

SOURCES=$(ROOTS:=.ced)
TARGETS=$(ROOTS:=.cede)

all: $(TARGETS)

%.cede : %.ced 
	@cedille $< ; if ( grep error $@ > /dev/null ) ; then echo "$<: ERROR"; else echo "$<"; fi

clean: 
	@rm $(TARGETS)
