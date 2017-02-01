#/bin/sh
NEDIT_FILES=$(find theories \( -name *.thy -or -name *.ML \) -type f)

# Open all .thy and .ML files inside the theories directory tree.
nedit $NEDIT_FILES
