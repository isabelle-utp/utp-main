#!/bin/sh
isabelle build -c -b HOL-Algebra2
# Session Kleene_Algebra does not seem to compile. Talk to Simon!
#isabelle build -c -b Kleene_Algebra
isabelle build -c -b Optics
isabelle build -c -b Continuum
isabelle build -c -b Dynamics
isabelle build -c -b UTP-IMPORTS
isabelle build -c -b UTP
isabelle build -c -b UTP-AX
isabelle build -c -b UTP-DEEP
isabelle build -c -b UTP-DEEP-AX
# Session UTP-HY-IMPORTS does not seem to compile. Talk to Simon!
#isabelle build -c -b UTP-HY-IMPORTS
# Session UTP-Hybrid depends on the above so does not compile either.
#isabelle build -c -b UTP-Hybrid
isabelle build -c -b VDM-SL
isabelle build -c -b FMI
