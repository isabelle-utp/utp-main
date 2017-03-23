#!/bin/sh
# Guess name of Isabelle/UTP home directory unless already set.
ISABELLE_UTP=${ISABELLE_UTP:-$(readlink -f $(dirname $0))/..}

# Directory for scripts and binary executables.
BIN_DIR=$ISABELLE_UTP/bin

# Remove AFP entry downloads
$BIN_DIR/afp_get.sh -d Kleene_Algebra
$BIN_DIR/afp_get.sh -d Ordinary_Differential_Equations

# Clean up document output directories
rm -rf $ISABELLE_UTP/axiomatic/output
rm -rf $ISABELLE_UTP/axiomatic/hierarchy/output
rm -rf $ISABELLE_UTP/dynamics/output
rm -rf $ISABELLE_UTP/fmi/output
rm -rf $ISABELLE_UTP/hybrid/output
rm -rf $ISABELLE_UTP/lenses/output
rm -rf $ISABELLE_UTP/tutorial/output
rm -rf $ISABELLE_UTP/utp/output
