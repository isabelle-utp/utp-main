#!/bin/bash
# Guess name of Isabelle/UTP home directory unless already set.
ISABELLE_UTP=${ISABELLE_UTP:-$(readlink -f $(dirname $0))/..}

# Directory for scripts and binary executables.
BIN_DIR=$ISABELLE_UTP/bin

# Determine installation directory for AFP downloads
AFP_INSTALL=${AFP_INSTALL:-$ISABELLE_UTP/contrib}

# Display usage information.

show_help() {
echo -e "\
\e[1mNAME\e[0m
    afp-get.sh - download AFP entry

\e[1mSYNOPSIS\e[0m
    ${0##*/} [-hd] [-v AFP_VERSION] [AFP_ENTRY]

\e[1mDESCRIPTION\e[0m
    Download the entry AFP_ENTRY from the Archive of Formal Proofs located at
    https://www.isa-afp.org/ and extract it to the directory specified by the
    environment variable AFP_INSTALL. If AFP_INSTALL is not set, the entry is
    downloaded to the ./contrib subdirectory of the current folder.

\e[1mOPTIONS\e[0m
    -h          display usage information
    -d          delete the AFP entry
    -u          use the development AFP
    -v AFP_VERSION  install a specific version (the default is current)"
}

# Initialize local variables.

AFP_VERSION="current"
AFP_URL="https://www.isa-afp.org/release/"
AFP_DEV="https://devel.isa-afp.org/release/"
AFP_FILE="afp-"
AFP_EXTENSION=".tar.gz"
AFP_DELETE=false

# Resetting OPTIND is necessary if getopts was used previously in the script.
# It is a good idea to make OPTIND local if you process options in a function.

OPTIND=1

# Check if on arguments given.

if [ $# -eq 0 ]
    then
        show_help
        exit 0
fi

# Otherwise parse options.

while getopts hduv: opt; do
    case $opt in
        h)
            show_help
            exit 0
            ;;
        d)  AFP_DELETE=true
            ;;
        u)  AFP_URL=$AFP_DEV
            ;;
        v)  AFP_VERSION=$OPTARG
            ;;
        *)
            show_help >&2
            exit 1
            ;;
    esac
done

# Shift off the options and optional --.

shift "$((OPTIND-1))"

# Construct URL for AFP file download.

AFP_ENTRY="$@"
AFP_FILE+="$AFP_ENTRY"
AFP_FILE+="-"
AFP_FILE+="$AFP_VERSION"
AFP_FILE+="$AFP_EXTENSION"
AFP_LINK="$AFP_URL$AFP_FILE"

# Create installation directory if it doesn't already exist

mkdir -p $AFP_INSTALL

# Perform download, file extraction and clean-up.

if [ "$AFP_DELETE" = true ]; then
  if [ -d "$AFP_INSTALL/$AFP_ENTRY" ]; then
    rm -r "$AFP_INSTALL/$AFP_ENTRY"
  else
    echo "AFP entry $AFP_ENTRY is not installed."
  fi
else if [ -d "$AFP_INSTALL/$AFP_ENTRY" ]; then
  echo "AFP entry $AFP_ENTRY is already installed."
else
  echo "Fetching $AFP_ENTRY from $AFP_URL..."
  wget -P $AFP_INSTALL $AFP_LINK
  if [ $? -eq 0 ]; then
    echo -n "Extracting $AFP_FILE..."
    cd $AFP_INSTALL
    tar xf $AFP_FILE
    rm $AFP_FILE
    cd - > /dev/null
    echo " [DONE]"
  else
    echo "Could not download $AFP_ENTRY."
  fi
fi
fi
# End of file
