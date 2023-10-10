#!/bin/bash
NO_THREADS=2

echo "Building Carl-parser ($1) in $2 configuration..."
# Checkout
git clone https://github.com/ths-rwth/carl-parser
mkdir build
cd build

cmake ..

# Build
make
cd ../..
echo "Building Carl-parser finished, do check for errors. If there is a error with path rerun cmake and make"
