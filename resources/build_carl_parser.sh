#!/bin/bash
NO_THREADS=2

# Get arguments
if [ $# -ne 2 ]; then
    echo "Usage: ./build_carl_parser.sh master|master14|<tag> release|debug"
    exit 1
fi
if [ "$1" == "master" ]; then
    MASTER=true
    MASTER14=false
else
    MASTER=false
    if [ "$1" == "master14" ]; then
        MASTER14=true
    else
        MASTER14=false
        LATEST_TAG="$1"
    fi
fi
if [ "$2" == "release" ]; then
    RELEASE=true
elif [ "$2" == "debug" ]; then
    RELEASE=false
else
    echo "Build mode must be 'release' or 'debug'."
    exit 2
fi

echo "Building Carl-parser ($1) in $2 configuration..."
# Checkout
git clone https://github.com/ths-rwth/carl-parser
cd carl-parser
if [ "$MASTER" = false ]; then
    if [ "$MASTER14" = true ]; then
        git checkout master14
    else
        git checkout tags/$LATEST_TAG
    fi
fi
mkdir build
cd build

# Configure
CMAKE_ARGS=""
if [ "$RELEASE" = true ]; then
    CMAKE_ARGS="-DCMAKE_BUILD_TYPE=Release"
else
    CMAKE_ARGS="-DCMAKE_BUILD_TYPE=Debug"
fi
cmake .. $CMAKE_ARGS

# Build
make carl-parser -j$NO_THREADS
cd ../..
echo "Building Carl-parser finished"
