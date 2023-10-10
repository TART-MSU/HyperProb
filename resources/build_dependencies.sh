#!/bin/bash

echo "Installing dependencies for carl, storm ..."

brew install git cmake 

brew install doxygen googletest boost gmp eigen

brew install cln ginac automake glpk hwloc z3 xerces-c

echo "If caused no errors, go ahead and build carl"