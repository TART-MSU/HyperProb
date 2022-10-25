#!/bin/bash
NO_THREADS=2

# Get arguments
if [ $# -ne 2 ]; then
    echo "Usage: ./build_pycarl.sh master|<tag> release|debug"
    exit 1
fi
if [ "$1" == "master" ]; then
    MASTER=true
else
    MASTER=false
    LATEST_TAG="$1"
fi
if [ "$2" == "release" ]; then
    RELEASE=true
elif [ "$2" == "debug" ]; then
    RELEASE=false
else
    echo "Build mode must be 'release' or 'debug'."
    exit 3
fi

echo "Building pycarl ($1) in $2 configuration..."

# Checkout
git clone https://github.com/moves-rwth/pycarl.git
cd pycarl
if [ "$MASTER" = false ]; then
    git checkout tags/$LATEST_TAG
fi
# Build
if [ "$RELEASE" = true ]; then
    python3 setup.py build_ext -j $NO_THREADS develop
else
    python3 setup.py build_ext --debug -j $NO_THREADS develop
fi
cd ..

echo "Building pycarl finished"