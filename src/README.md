 # Lean source files

All of your Lean source files should live below the /src project directory, and you must maintain files in /src according to the following rules.

## /src/instructor

The /src/instructor directory is where Prof. Sullivan will put files for you.  

*Do not* create, edit, or delete files in this directory, otherwise you will encounter git *merge conflicts*, which occur when your local changes to a file or directory conflict with those made to the *upstream* repository by Prof. Sullivan. 

Download new or changed files from Prof. Sullivan using the following command, entered in a terminal/shell.

``` sh
git pull upstream main
```

## /src/mywork

The /src/mywork directory is where you should do your work. You will sometimes want to edit files that Prof. Sullivan provides. To do this copy the files from /src/sullivan to /src/mywork *before* you edit them. You may then edit your copies. 

To push changes you've made locally to your GitHub repository, issue the following commands in a terminal window.

``` sh
git add .
git commit -m "a short message describing your changes"
git push
```

## /src/test

Here you'll find a single file that you can use to determine whether your system is working correctly.
