#!/bin/bash
NO_THREADS=2

# Checkout
git clone https://github.com/moves-rwth/pycarl.git
cd pycarl
# Build
python3 setup.py develop
cd ..

echo "Building pycarl finished"