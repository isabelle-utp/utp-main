#/bin/sh
isabelle build -c -b HOL-UTP-IMPORTS
isabelle build -c -b HOL-UTP
isabelle build -c -b HOL-UTP-DES
isabelle build -c -b HOL-UTP-THY
#The CML model still needs to be recast in terms of the new model framework.
#isabelle build -c -b HOL-UTP-CML
