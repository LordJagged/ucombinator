# The HOFA build script.

WINTITLE="Higher-order flow analysis engine"

# Toolchain.
SCALAC=scalac
SCALA=scala
SCALADOC=scaladoc



# Directories.
SRC=src
BIN=bin
LIB=lib
DOC=doc
CP=$(LIB):../../code/scala/lib:../../projects/lambdo/lib


# Principal files.
SCALA_FILES=$(shell find $(SRC) -name '*.scala')
CLASS_FILES=$(patsubst src/%,lib/%,$(SCALA_FILES:.scala=.class))

DOCINDEX=$(DOC)/index.html

# Commands
SC=$(SCALAC) -cp $(CP) -d $(LIB)
SCALA_BIGMEM=java -Xmx1024M -Xmn1024M -cp .:/opt/local/share/java/scala-library.jar:$(CP)


# Top-level rules.
.PHONY: default
default: allcode

.PHONY: all
all: $(CLASS_FILES) $(DOCINDEX) $(BIN)/hofa.run

.PHONY: allcode
allcode: $(CLASS_FILES)

.PHONY: force
force: # Forcibly rebuild everything.
	@echo Compiling all files...
	@ $(SC) -unchecked $(SCALA_FILES)

.PHONY: prompt
prompt:	
	$(SCALA) -cp $(CP)

# Build rules.
$(CLASS_FILES): $(SCALA_FILES)
	@echo Compiling modified files only:
	@echo " "$(notdir $?)
	@echo " Use 'make force' to forcibly compile everything."
	@ $(SC) $?
	@touch $(CLASS_FILES)

$(DOCINDEX): $(SCALA_FILES)
	@echo Generating documentation...
	@ $(SCALADOC) -cp $(CP) -windowtitle $(WINTITLE) -d $(DOC) $^

$(BIN)/hofa.run: Makefile
	@echo Creating hofa.run script...
	@echo $(SCALA_BIGMEM) org.ucombinator.project.hofa.\$$1 \$$2 \$$3 \$$4 \$$5 \$$6 \$$7 \$$8 \$$9 > bin/hofa.run
	@chmod u+x $(BIN)/hofa.run



# Clean up rules.
clean:
	rm -rf $(LIB)/* $(DOC)/* $(BIN)/hofa.run




