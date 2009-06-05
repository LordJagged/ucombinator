# The Lambdo project build script.

WINTITLE="Lambdo"

# Binaries.
SCALAC=fsc
SCALA=scala
SCALADOC=scaladoc

# Directories.
SRC=src
DOC=doc
LIB=lib
CP=$(LIB):../../code/scala/lib

UCDIR=$(LIB)/org/ucombinator
PROJECTDIR=$(UCDIR)/project
LAMBDODIR=$(PROJECTDIR)/lambdo

# Principal files.
DOCINDEX=doc/index.html
LAMBDOCLASS=$(LAMBDODIR)/Lambdo.class
CPSTRANSFORMERCLASS=$(LAMBDODIR)/CPSTransformer.class
UNDEFINERCLASS=$(LAMBDODIR)/Undefiner.class
ANORMALIZERCLASS=$(LAMBDODIR)/ANormalizer.class
UNTAILERCLASS=$(LAMBDODIR)/Untailer.class


# Make all.
all: allcode alldocs

# Run rules.
runlambdo: $(LAMBDOCLASS)
	$(SCALA) -cp $(CP) org.ucombinator.project.lambdo.Lambdo



# Build rules.
allcode: $(LAMBDOCLASS) $(CPSTRANSFORMERCLASS) $(UNDEFINERCLASS) $(ANORMALIZERCLASS) $(UNTAILERCLASS)

alldocs: $(DOCINDEX) 


$(DOCINDEX): $(SRC)/*.scala
	$(SCALADOC) -cp $(CP) -d doc -windowtitle $(WINTITLE) $(SRC)/*

$(LAMBDOCLASS): $(SRC)/Lambdo.scala
	$(SCALAC) -cp $(CP) -d $(LIB) $(SRC)/Lambdo.scala

$(CPSTRANSFORMERCLASS): $(SRC)/CPSTransformer.scala
	$(SCALAC) -cp $(CP) -d $(LIB) $(SRC)/CPSTransformer.scala

$(UNDEFINERCLASS): $(SRC)/Undefiner.scala
	$(SCALAC) -cp $(CP) -d $(LIB) $(SRC)/Undefiner.scala

$(ANORMALIZERCLASS): $(SRC)/ANormalizer.scala
	$(SCALAC) -cp $(CP) -d $(LIB) $(SRC)/ANormalizer.scala

$(UNTAILERCLASS): $(SRC)/Untailer.scala
	$(SCALAC) -cp $(CP) -d $(LIB) $(SRC)/Untailer.scala




# Clean up rules.
clean:
	fsc -shutdown
	rm -rf $(LIB)/* $(DOC)/*




