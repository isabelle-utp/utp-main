#/bin/sh

# Find all .thy and .ML files inside the utp directory tree.
NEDIT_FILES=$(find utils utp exercises tutorial vdm-sl \( -name *.thy -or -name *.ML \) -type f)

nedit $NEDIT_FILES
