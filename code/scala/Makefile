# The U Combinator public library

WINTITLE="U Combinator"

# Toolchain.
SCALAC=scalac
SCALA=scala
SCALADOC=scaladoc


# Directories.
SRC=src
BIN=bin
LIB=lib
DOC=doc


# Principal files.
SCALA_FILES=$(shell find $(SRC) -name '*.scala')
CLASS_FILES=$(patsubst src/%,lib/%,$(SCALA_FILES:.scala=.class))

DOCINDEX=$(DOC)/index.html

# Commands
SC=$(SCALAC) -d $(LIB)


# Top-level rules.
.PHONY: default
default: all

.PHONY: all
all: $(CLASS_FILES) $(DOCINDEX)

.PHONY: force
force: # Forcibly rebuild everything.
	$(SC) $(SCALA_FILES)


# Build rules.
$(CLASS_FILES): $(SCALA_FILES)
	@echo Compiling modified files: $(notdir $?)
	$(SC) $?
	touch $(CLASS_FILES)

#lib/%.class: src/%.scala
#	$(SC) $<

$(DOCINDEX): $(SCALA_FILES)
	$(SCALADOC) -windowtitle $(WINTITLE) -d $(DOC) $^



# Clean up rules.
.PHONY: clean
clean:
	rm -rf $(LIB)/* $(DOC)/*




