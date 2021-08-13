# Introduction

This project is a client of LeanVM.
# Boot Lean via VSCode Remote to container
- Prerequisites
  - docker installed
  - leanvm image pulled
- Postrequisites
  - Develop inside a container: https://code.visualstudio.com/docs/remote/containers
  - https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.vscode-remote-extensionpack
  - avoid  Home 2004+ with WSL2 enabled, WSL not needed when on Windows Pro!
  - https://code.visualstudio.com/docs/remote/create-dev-container
  - 
  - leanvm launchable---cd to project dir, run "leanvm", get "lean vm proj_name `pwd`"
  - vscode connectable (command line argument available to specify docker image?)
    - autoload recommendeds
    - 
# Template for Lean Using kevinsullivan/clean_lean and VSCode with Remote Development 

- Prerequisite: You alread have Lean and mathlib installed and you can run the leanproject command.

- Postrequisite: 
  - a new Lean project (at a specific path) up and running
  - the project is pushed to a corresponding new GitHub git repo
  - container with project name is running with project directory mounted on its /hostdir mount point
    - run_leanvm local_container_name local_directory_path
  - VSCode is connected to a containerized Lean 
    - necessary packages installed via recommended packages field of .vscode file
## Create Lean Project Locally

Create a new Lean project on your computer.
In this example, the project name is dm2120,
``` sh
leanproject new dm2120```
```

### Push to new Upstream Git Repo

Push the project to to a new git repository,
https://github.com/kevinsullivan/dm2120.git.
``` sh
cd dm2120
git remote add origin https://github.com/kevinsullivan/dm2120-dev.git
git push --set-upstream origin master
```

### Build the new project
``` sh
leanproject build 
```

### Run leanvm in Docker
``` sh 
docker pull kevinsullivan/clean_lean
launch leanvm on dm2120
```


