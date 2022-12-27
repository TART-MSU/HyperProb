# Base Dockerfile for using HyperProb
###################################

FROM movesrwth/stormpy:1.7.0

# Install dependencies
######################

WORKDIR /opt/

# Obtain latest version of HyperProb from public repository
RUN git clone -b master https://github.com/TART-MSU/HyperProb.git

# Switch to HyperProb directory
WORKDIR /opt/HyperProb

# Install dependencies for HyperProb
RUN pip3 install .
