#!/bin/bash
# Guess name of Isabelle/UTP home directory unless already set.
ISABELLE_UTP=${ISABELLE_UTP:-$(readlink -f $(dirname $0))/..}

# Directory for scripts and binary executables.
BIN_DIR=$ISABELLE_UTP/bin
CONTRIB_DIR=$ISABELLE_UTP/contrib

printf "Checking and obtaining Isabelle/UTP AFP dependencies... \n\n"

# Download required AFP entries
while read in; do $BIN_DIR/afp_get.sh -u "$in" ; done < $CONTRIB_DIR/ROOTS
