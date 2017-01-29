#!/bin/sh
isabelle build -c -b UTP-DEPS
isabelle build -c -b UTP-IMPORTS
isabelle build -c -b UTP-IMPORTS-AX
isabelle build -c -b UTP
isabelle build -c -b UTP-AX
isabelle build -c -b VDM-SL