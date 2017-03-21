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
# Library Components
isabelle build -d $ROOT -c -b HOL-Algebra2
isabelle build -d $ROOT -c -b Optics
isabelle build -d $ROOT -c -b Continuum
isabelle build -d $ROOT -c -b Dynamics
# Core UTP Framework
isabelle build -d $ROOT -c -b UTP-IMPORTS
isabelle build -d $ROOT -c -b UTP
isabelle build -d $ROOT -c -b UTP-DEEP
isabelle build -d $ROOT -c -b UTP-AXM
isabelle build -d $ROOT -c -b UTP-DEEP-AXM
# UTP Theory Base
isabelle build -d $ROOT -c -b UTP-THY
isabelle build -d $ROOT -c -b UTP-THY-DEEP
isabelle build -d $ROOT -c -b UTP-THY-AXM
isabelle build -d $ROOT -c -b UTP-THY-DEEP-AXM
# Hybrid UTP
isabelle build -d $ROOT -c -b UTP-HYBRID-IMPORTS
isabelle build -d $ROOT -c -b UTP-HYBRID
# Languages and Mechanisations
isabelle build -d $ROOT -c -b VDM-SL
isabelle build -d $ROOT -c -b UTP-TUTORIAL
isabelle build -d $ROOT -c -b FMI
