#!/bin/bash

echo "Installing dependencies for carl, storm ..."
brew install git cmake 

# Skipping this because you should have clang from apple itself
#brew install llvm

brew install doxygen googletest boost gmp eigen

brew install cln ginac automake glpk hwloc z3 xerces-c


echo "If caused no errors, go ahead and build carl"