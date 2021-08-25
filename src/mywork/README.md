# Your working directory

The /src/mywork directory is where you should do all of your work for this class. When you're creating, editing, or deleting files in this directory using VSCode, you will actually be operating on a *clone* (a copy that knows where it came from) of your GitHub repository stored in a *Docker container* running on your own computer. To *push* all of the changes you've made locally back to your GitHub repository, run the following command in a terminal window, or use the corresponding functions within VSCode (we'll show you how).

``` sh
git add .                                       # stage changed files to be added to your local clone
git commit -m "<description of what changed>"   # add the staged changes to your local clone 
git push origin main                            # now make those changes to your GitHub repository
```

It's very important to push your local changes to your GitHub repository regularly, so that you don't accidentally lose work should the Docker container storing your local clone be lost or damaged. We might also ask you to submit work by pushing it to your repository (which must be set to be a private GitHub repository).
