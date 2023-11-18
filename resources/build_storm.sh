#!/bin/bash
#
NO_THREADS=6
# have only one carl version installed, else if there is a carl in local/lib, storm will fail to read the local installation of carl
# use ccmake .. to

# Checkout
git clone https://github.com/moves-rwth/storm.git
cd storm
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