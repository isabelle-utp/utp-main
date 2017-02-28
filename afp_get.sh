#!/bin/bash

AFP_INSTALL=${AFP_INSTALL:-./contrib/}

# Usage info
show_help() {
cat << EOF
Usage: ${0##*/} [-hd] [-v VERSION] [AFP_ENTRY]...
Download an entry from the Archive of Formal Proofs
EOF
}

# Initialize our own variables:
entry=""
version="current"
afp_url="https://www.isa-afp.org/release/"
afp_file="afp-"
afp_extension=".tar.gz"
afp_delete=false

OPTIND=1
# Resetting OPTIND is necessary if getopts was used previously in the script.
# It is a good idea to make OPTIND local if you process options in a function.

while getopts hdv: opt; do
    case $opt in
        h)
            show_help
            exit 0
            ;;
        d)  afp_delete=true
            ;;
        v)  version=$OPTARG
            ;;
        *)
            show_help >&2
            exit 1
            ;;
    esac
done
shift "$((OPTIND-1))" # Shift off the options and optional --.

afp_file+="$@"
afp_file+="-"
afp_file+="$version"
afp_file+="$afp_extension"
afp_url+="$afp_file"

if [ "$afp_delete" = true ]; then
  if [ -d "$AFP_INSTALL/$@" ]; then
    rm -r "$AFP_INSTALL/$@"
  else
    echo "AFP entry $@ is not installed."    
  fi   
else if [ -d "$AFP_INSTALL/$@" ]; then
  echo "AFP entry $@ is already installed."
else
  echo "Fetching $@..."
  wget -P $AFP_INSTALL $afp_url
  if [ $? -eq 0 ]; then
    echo "Extracting..."
    cd $AFP_INSTALL
    tar xf $afp_file
    rm $afp_file
    cd - > /dev/null
  else
    echo "Could not download $@."
  fi
fi
fi

# End of file
