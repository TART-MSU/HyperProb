#!/bin/bash
NO_THREADS=6

echo "Building Carl for storm"
# Checkout this master14 repo specially made for storm and stormpy
git clone https://github.com/moves-rwth/carl-storm
cd carl-storm && mkdir build && cd build
cmake ..

# Build
make lib_carl -j$NO_THREADS
cd ../..
echo "Building Carl finished, do check for errors"