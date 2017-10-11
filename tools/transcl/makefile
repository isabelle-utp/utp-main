################################################################################
# Makefile for compilation of the transcl executable, 2017 (c) by Frank Zeyda  #
################################################################################

# We require echo, mkdir, rm, wget, sed, tar and g++ to be installed.

# Configuration of the source, library and build directories.
SRC_DIR=src
LIB_DIR=lib
TMP_DIR=build
DOC_DIR=isabelle/output

# Create build directory.
MK_TMP_DIR:=$(shell mkdir -p $(TMP_DIR))

# C source and header files.
SRC_FILES:=$(wildcard $(SRC_DIR)/*.c)
HDR_FILES:=$(wildcard $(SRC_DIR)/*.h)

# C++ source and header files.
CPP_FILES:=$(wildcard $(SRC_DIR)/*.cpp)
HPP_FILES:=$(wildcard $(SRC_DIR)/*.hpp)

# C/C++ object files.
OBJ_FILES:=\
$(patsubst $(SRC_DIR)/%.c,$(TMP_DIR)/%.o,$(SRC_FILES)) \
$(patsubst $(SRC_DIR)/%.cpp,$(TMP_DIR)/%.o,$(CPP_FILES))

# C/C++ dependency files.
DEP_FILES:=\
$(patsubst $(SRC_DIR)/%.c,$(TMP_DIR)/%.d,$(SRC_FILES)) \
$(patsubst $(SRC_DIR)/%.cpp,$(TMP_DIR)/%.d,$(CPP_FILES))

# URL to download the C++ Boost library.
BOOST_TAR=boost_1_64_0.tar.gz
BOOST_EXT=boost_1_64_0/boost
BOOST_URL=https://dl.bintray.com/boostorg/release/1.64.0/source/$(BOOST_TAR)

# Location of the Boost library headers.
BOOST_LIB=$(LIB_DIR)/boost_1_64_0

all: transcl isabelle

transcl: $(OBJ_FILES)
	g++ -std=c++17 -O3 -I$(SRC_DIR) -I$(BOOST_LIB) $(OBJ_FILES) -o transcl

# Rule for downloading and extracting the C++ Boost library.
$(BOOST_LIB):
	@echo "Downloading C++ Boost library..."
	wget $(BOOST_URL) -nv --show-progress -P $(LIB_DIR)
	@echo "Unpacking C++ Boost library..."
	tar xzf $(LIB_DIR)/$(BOOST_TAR) -C $(LIB_DIR) $(BOOST_EXT)
	rm $(LIB_DIR)/$(BOOST_TAR)

# Pattern rules for compilation of C/C++ source files.
$(TMP_DIR)/%.o: src/%.c $(BOOST_LIB)
	g++ -std=c++17 -O3 -I$(SRC_DIR) -I$(BOOST_LIB) -c $< -o $@

$(TMP_DIR)/%.o: src/%.cpp $(BOOST_LIB)
	g++ -std=c++17 -O3 -I$(SRC_DIR) -I$(BOOST_LIB) -c $< -o $@

# Pattern rules for generating dependency (make)files
$(TMP_DIR)/%.d: src/%.c $(BOOST_LIB)
	@set -e; rm -f $@; \
	g++ -std=c++17 -I$(SRC_DIR) -I$(BOOST_LIB) -MM $< -o $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,$(TMP_DIR)/\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

$(TMP_DIR)/%.d: src/%.cpp $(BOOST_LIB)
	@set -e; rm -f $@; \
	g++ -std=c++17 -I$(SRC_DIR) -I$(BOOST_LIB) -MM $< -o $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,$(TMP_DIR)/\1.o $@: ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

# Conditional inclusion avoids download of C++ Boost when the target is clean.
ifneq ($(MAKECMDGOALS),clean)
-include $(DEP_FILES)
endif

isabelle:
	isabelle build -d. -c HOL-TRANSCL

clean:
	rm -rf $(TMP_DIR) $(DOC_DIR) $(LIB_DIR)/* transcl

.PHONY: all isabelle clean
