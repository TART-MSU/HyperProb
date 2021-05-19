---
layout: page
title: Docker
permalink: /docker/
description: What is it and how to run it
---
[Docker](https://www.docker.com/ "Docker") helps deploy small and lightweight execution environments which shares your operating system kernel but otherwise run in isolation from each other. It has helped popularize the concept of containerization.

![docker_vm](../assets/images/docker_vm.png)
<div style="text-align: center;"> Figure: Virtual machines vs Docker Containers </div>
<br> 
The above picture (borrowed from [here](https://www.docker.com/blog/containers-replacing-virtual-machines/ "docker_vs_vm"), read the post for an elaborate explaination). The idea is that from a docker image, we can create several containers, which will run in isolation by mainly using our host operating system.

We chose this solution to deploy the tool so that the users can avoid the installation process for the dependencies, that have already been included in our docker image. As seen below to run a container with the tool, you can find the neccesary image [here on docker hub](https://hub.docker.com/r/oyendrila/hyperprob "hub"). This has been built using an existing image with the dependencies (CArL, cral-parser, pyCArL, storm amd stormpy) created by RWTH Aachen, available [here](https://hub.docker.com/r/movesrwth/stormpy "doc_img"). 

![docker_img](../assets/images/docker.png)
<div style="text-align: center;"> Figure: Docker workflow </div>
<br> 

To be able to run this image on your machine, 
- Download and install docker on your system from [here](https://docs.docker.com/desktop/ "doc_link")