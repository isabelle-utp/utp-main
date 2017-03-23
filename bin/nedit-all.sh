#/bin/sh
# Guess name of Isabelle/UTP home directory unless already set.
ISABELLE_UTP=${ISABELLE_UTP:-$(readlink -f $(dirname $0))/..}

# Folders in which to look for .thy and .ML files.
LOOK_INSIDE="axiomatic continuum deep dynamics exercises fmi hybrid lenses theories tutorial utils utp vdm-sl"

# Find all .thy and .ML files inside the utp directory tree.
NEDIT_FILES=$(find $ISABELLE_UTP/$LOOK_INSIDE \( -name *.thy -or -name *.ML \) -type f)

# A poor-mans refactoring facility: use *Multiple Documents* Replace/Find.
nedit $NEDIT_FILES
