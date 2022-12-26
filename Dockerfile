# Base Dockerfile for using stormpy
###################################
# The Docker image can be built by executing:
# docker build -t yourusername/stormpy .

FROM movesrwth/stormpy:1.6.3


# Install dependencies
######################

WORKDIR /opt/
# Obtain latest version of HyperProb from public repository
RUN git clone -b master https://github.com/TART-MSU/HyperProb.git

# Switch to HyperProb directory
WORKDIR /opt/HyperProb

# Build pycarl
RUN python3 setup.py build_ext -j $no_threads develop



# Build stormpy
###############
RUN mkdir /opt/stormpy
WORKDIR /opt/stormpy

# Copy the content of the current local stormpy repository into the Docker image
COPY . .

# Build stormpy
RUN python3 setup.py build_ext -j $no_threads develop