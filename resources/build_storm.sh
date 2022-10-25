#!/bin/bash
NO_THREADS=6

# Get arguments
if [ $# -ne 3 ]; then
    echo "Usage: ./build_storm.sh master|<tag> release|debug target"
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
TARGET=$3

echo "Building Storm ($1) target $3 in $2 configuration..."
# Checkout
git clone https://github.com/moves-rwth/storm.git
cd storm
if [ "$MASTER" = false ]; then
    git checkout tags/$LATEST_TAG
fi
mkdir build
cd build

# Configure
CMAKE_ARGS="-DSTORM_PORTABLE=ON"
if [ "$RELEASE" = true ]; then
    CMAKE_ARGS="-DCMAKE_BUILD_TYPE=Release -DSTORM_DEVELOPER=OFF -DSTORM_LOG_DISABLE_DEBUG=ON $CMAKE_ARGS"
else
    CMAKE_ARGS="-DCMAKE_BUILD_TYPE=Debug -DSTORM_DEVELOPER=ON -DSTORM_LOG_DISABLE_DEBUG=OFF $CMAKE_ARGS"
fi
cmake .. $CMAKE_ARGS

# Build
make $TARGET -j$NO_THREADS
cd ../..
echo "Building Storm finished"