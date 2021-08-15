# Boot

Copyright 2021 Rector and Visitors of the University of Virginia.
Author: Kevin Sullivan, UVA CS Department, sullivan@virginia.edu

This document provides our method for cloning a suitable git repo
into a local Docker volume for remote development in our LeanVM
containerized development environment. 

Precondition: your physical host computer use Windows or MacOS (*).

Postcondition: you will be editing a new containerized clone
of your repo though a nicely configured VSCode IDE. 

- Update your operating system
  - case OS
    - Windows: Update to Windows Education 
      - Get license key from ITS
      - Use Windows Update to install key to activate update
    - MacOS: Be sure your OS is completely up-to-date
- Have a GitHub account
- Install Docker Desktop: https://www.docker.com/products/docker-desktop
- Install VSCode: https://code.visualstudio.com/download
- Fork this very repository now
- Launch new VSCode window
- VSCode Command "Remote-Container to clone" with your repo as the argument
- Wait for everything to boot up, as signalled by ____

You now have a Lean development environment with a container
provided volume holding a clone of your repository. You push
to and pull from your fork from the container as you see fit.

(*) Why? Some required Docker functions are not yet implemented for
Docker running on Linux hosts.
