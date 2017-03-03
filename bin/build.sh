#!/bin/sh
# Guess name of Isabelle/UTP home directory unless already set.
ISABELLE_UTP=${ISABELLE_UTP:-$(readlink -f $(dirname $0))/..}

# Directory for scripts and binary executables.
BIN_DIR=$ISABELLE_UTP/bin

# Download required AFP entries
$BIN_DIR/afp_get.sh Kleene_Algebra
$BIN_DIR/afp_get.sh Ordinary_Differential_Equations

ROOT=$ISABELLE_UTP

# Build all heap images of Isabelle/UTP
isabelle build -d $ROOT -c -b HOL-Algebra2
isabelle build -d $ROOT -c -b Optics
isabelle build -d $ROOT -c -b Continuum
isabelle build -d $ROOT -c -b Dynamics
isabelle build -d $ROOT -c -b UTP-IMPORTS
isabelle build -d $ROOT -c -b UTP
isabelle build -d $ROOT -c -b UTP-AX
isabelle build -d $ROOT -c -b UTP-DEEP
isabelle build -d $ROOT -c -b UTP-DEEP-AX
isabelle build -d $ROOT -c -b UTP-HYBRID-IMPORTS
isabelle build -d $ROOT -c -b UTP-HYBRID
isabelle build -d $ROOT -c -b VDM-SL
isabelle build -d $ROOT -c -b UTP-TUTORIAL
isabelle build -d $ROOT -c -b FMI
