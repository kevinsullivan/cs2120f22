# How to set up a Lean project

To set up a new Lean project on your computer
do the following.

### Create Lean Project Locally

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

