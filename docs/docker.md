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
The above picture (borrowed from [here](https://www.docker.com/blog/containers-replacing-virtual-machines/ "docker_vs_vm"), read the post for an elaborate explaination). The idea is that from a docker image, we can create several containers, which will run in isolation by mainly using our host operating system. Please note that docker only provides a <i>command line user interface</i> to interact with the containers.

We chose this solution to deploy the tool so that the users can avoid the installation process for the dependencies, that have already been included in our docker image. As seen below to run a container with the tool, you can find the neccesary image [here on docker hub](https://hub.docker.com/r/oyendrila/hyperprob "hub"). This has been built using an existing image with the dependencies (CArL, carl-parser, pyCArL, storm, stormpy, and z3) created by RWTH Aachen, available [here](https://hub.docker.com/r/movesrwth/stormpy "doc_img"). 

![docker_img](../assets/images/docker.png)
<div style="text-align: center;"> Figure: Docker workflow </div>
<br> 

To be able to run this image on your machine, 
- Download and install docker desktop on your system from [here](https://docs.docker.com/desktop/ "doc_link").<br>
- On your command line interface, the command `docker` should give you a help menu.
- Pull the image by using the command, `docker pull oyendrila/hyperprob`.
- The command `docker images` should give you details of the image.
- To create a container out of this image and run it, use the command <br>
`docker run -it oyendrila/hyperprob /bin/bash` <br> The control in your terminal will shift to bash inside this and start in the `/opt` folder. Feel free to explore the container. For details on how to use the tool, refer to the [tool usage tab](tool_usage/ "tool_usage tab").
- To exit the container, just type `exit` and the control will shift to your native terminal.
- The `docker run` that we invoked earlier would stop the container on exit. the command `docker ps -a` should list all your containers, along with its name (for example say, 'loving_lederberg').
- To restart the above container, use `docker exec -it loving_lederberg /bin/bash `. 