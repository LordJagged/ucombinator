# The Lambdo project build script.

WINTITLE="Lambdo"

# Binaries.
SCALAC=fsc
SCALA=scala
SCALADOC=scaladoc

# Directories.
SRC=src
BIN=bin
DOC=doc
CP=$(BIN):../../code/scala/lib

UCDIR=$(BIN)/org/ucombinator
PROJECTDIR=$(UCDIR)/project
LAMBDODIR=$(PROJECTDIR)/lambdo

# Principal files.
DOCINDEX=doc/index.html
LAMBDOCLASS=$(LAMBDODIR)/Lambdo.class
CPSTRANSFORMERCLASS=$(LAMBDODIR)/CPSTransformer.class
UNDEFINERCLASS=$(LAMBDODIR)/Undefiner.class
ANORMALIZERCLASS=$(LAMBDODIR)/ANormalizer.class


# Make all.
all: allcode alldocs

# Run rules.
runlambdo: $(LAMBDOCLASS)
	$(SCALA) -cp $(CP) org.ucombinator.project.lambdo.Lambdo



# Build rules.
allcode: $(LAMBDOCLASS) $(CPSTRANSFORMERCLASS) $(UNDEFINERCLASS) $(ANORMALIZERCLASS)

alldocs: $(DOCINDEX) 


$(DOCINDEX): $(SRC)/*.scala
	$(SCALADOC) -cp $(CP) -d doc -windowtitle $(WINTITLE) $(SRC)/*

$(LAMBDOCLASS): $(SRC)/Lambdo.scala
	$(SCALAC) -cp $(CP) -d $(BIN) $(SRC)/Lambdo.scala

$(CPSTRANSFORMERCLASS): $(SRC)/CPSTransformer.scala
	$(SCALAC) -cp $(CP) -d $(BIN) $(SRC)/CPSTransformer.scala

$(UNDEFINERCLASS): $(SRC)/Undefiner.scala
	$(SCALAC) -cp $(CP) -d $(BIN) $(SRC)/Undefiner.scala

$(ANORMALIZERCLASS): $(SRC)/ANormalizer.scala
	$(SCALAC) -cp $(CP) -d $(BIN) $(SRC)/ANormalizer.scala




# Clean up rules.
clean:
	fsc -shutdown
	rm -rf $(BIN)/* $(DOC)/*




