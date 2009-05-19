# The U Combinator build script.

WINTITLE="U Combinator library"

# Binaries.
SCALAC=scalac
SCALA=scala

# Directories.
SRC=src
BIN=bin
LIB=lib
DOC=doc

UCDIR=$(LIB)/org/ucombinator
LANGDIR=$(UCDIR)/lang
UTILDIR=$(UCDIR)/util
CPSDIR=$(UTILDIR)/cps
LANGUAGESDIR=$(UCDIR)/languages
SEXPDIR=$(LANGUAGESDIR)/sexp


# Principal files.
SEXPCLASS=$(SEXPDIR)/SExp.class
SYNTAXNODECLASS=$(LANGUAGESDIR)/SyntaxNode.class 
EXTENSIBLECLASS=$(LANGDIR)/Extensible.class
CPSUTILCLASS=$(CPSDIR)/CPSUtil.class
DOCINDEX=$(DOC)/index.html


# Build rules.
all: $(DOCINDEX) $(SEXPCLASS) $(SYNTAXNODECLASS) $(CPSUTILCLASS)

$(DOCINDEX): $(SRC)/*.scala
	scaladoc -windowtitle $(WINTITLE) -d $(DOC) $(SRC)/*.scala

$(SEXPCLASS): $(SRC)/SExp.scala
	$(SCALAC) -d $(LIB) $(SRC)/SExp.scala

$(SYNTAXNODECLASS): $(SRC)/SyntaxNode.scala $(EXTENSIBLECLASS)
	$(SCALAC) -d $(LIB) $(SRC)/SyntaxNode.scala

$(EXTENSIBLECLASS): $(SRC)/Extensible.scala
	$(SCALAC) -d $(LIB) $(SRC)/Extensible.scala

$(CPSUTILCLASS): $(SRC)/CPSUtil.scala
	$(SCALAC) -d $(LIB) $(SRC)/CPSUtil.scala



# Clean up rules.
clean:
	rm -rf $(BIN)/* $(LIB)/* $(DOC)/*




