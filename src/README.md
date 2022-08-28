# Using this project

This file explains how to use this project.

## /src/test

In the /src/test subdirectory, you'll find a two files. Open each of them up to check whether your system is working correctly. The lean_test file tells you how to know that the Lean Prover is working, and the python_test file is to determine whether Python is working: look for the arrow in the right upper corner to run the Hello World program, and give it a push.

## /src/instructor

The /src/instructor directory is where Prof. Sullivan will put files for you.  *Do not* create, edit, or delete files in this directory, otherwise you will encounter git *merge conflicts*, which occur when your local changes to a file or directory conflict with those made to the *upstream* repository by Prof. Sullivan. Download new or changed files from Prof. Sullivan using the following command, entered in a terminal/shell.

``` sh
git pull upstream main
```

## /src/mywork

The /src/mywork directory is where you should do your work. You will sometimes want to edit files that Prof. Sullivan provides. To do this copy the files from /src/sullivan to /src/mywork *before* you edit them. You may then edit your copies. To push changes you've made in VSCode to your own local GitHub repository, issue the following commands in a terminal window.

``` sh
git add .
git commit -m "a short message describing your changes"
git push
```

