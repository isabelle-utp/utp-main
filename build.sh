#!/bin/sh

# Collect necessary AFP entries
./afp_get.sh Kleene_Algebra
./afp_get.sh Ordinary_Differential_Equations

# Build all heap images of Isabelle/UTP
isabelle build -d. -c -b HOL-Algebra2
isabelle build -d. -c -b Optics
isabelle build -d. -c -b Continuum
isabelle build -d. -c -b Dynamics
isabelle build -d. -c -b UTP-IMPORTS
isabelle build -d. -c -b UTP
isabelle build -d. -c -b UTP-AX
isabelle build -d. -c -b UTP-DEEP
isabelle build -d. -c -b UTP-DEEP-AX
isabelle build -d. -c -b UTP-HY-IMPORTS
isabelle build -d. -c -b UTP-Hybrid
isabelle build -d. -c -b VDM-SL
isabelle build -d. -c -b UTP-Tutorial
isabelle build -d. -c -b FMI
