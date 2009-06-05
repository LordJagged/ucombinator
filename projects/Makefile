#include ../share/make/Makefile-dir

ORDER=lambdo hofa

all:
	for d in $(ORDER); do cd $$d; echo compiling: $$d; make all; cd ..; done

clean:
	for d in $(ORDER); do cd $$d; echo cleaning: $$d; make clean; cd ..; done



