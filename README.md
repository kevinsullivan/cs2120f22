# Create a Lean IDE using VSCode Remote Containers

The purpose of this document is to guide you through the process of setting up a VSCode-based development environment for writing logic and mathematics using the Lean Prover. We've worked hard to make this possible while installing minimal software onto your own machine. 
You must be running a computer that runs either the Windows or MacOS operating system. Here are the steps.

- Update your operating system:
  - by cases:
    - if MacOS: Be sure your OS is completely up-to-date (current version of Big Sur, currently 11.5.1 as of this writing).
    - if Windows: Update to Windows Education, which is an educational version of Windows 10 Enterprise (Windows 10 Home won't do).
      - Get OS Windows Update license key from ITS: https://virginia.service-now.com/its/.  
      - Click Software in the left-hand navigation. Select the *latest* Windows 10 Education version. Get an update key.
      - After obtaining the OS key, copy and paste it in to the Windows Activation page (same screen as Windows Update).
      - Reboot your machine. You can check the Windows *System Information* app to confirm that your OS is updated.
- Have a GitHub account. Create one for yourself if necessary. It's free.
- Install Docker Desktop: https://www.docker.com/products/docker-desktop.
- Install VSCode: https://code.visualstudio.com/download.
- Fork this repository now.
  - You must be logged in to your GitHub account.
  - Visit this very repository page: https://github.com/kevinsullivan/cs2120 (which is probably where you're reading this)
  - Fork this repo using the *Fork* command in the upper right corner. This will create a copy of this entire repository in *your* GitHub account. Visit your GitHub page to confirm that you now have a cs2120 repository. Select the gren Code button, then HTTPS, then copy the URL that is provided. This will be the GitHub URL of your fork of the cs2120 respository.
- Launch a new VSCode window. Use CTRL-SHIFT-P to bring up the VSCode command palatte. Type in and select *Clone Repository in Container Volume* and then paste the URL of your new repository as the argument.
- Wait a few minutes for your development environment to boot up, then you're ready to go.
- Check to see that everything is working by opening the test.lean file and checking that the conditions described therein are satisfied.

What you now have is a complete VSCode-based interactive development environment for using the Lean Prover and its math library. This development environment is provided by a *Docker container* running Linux (Ubuntu 20.04 LTS) configured with all the necessary software. You should not have to install any software beyond Docker Desktop and VSCode on your host (laptop) computer. In addition to running our Linux OS, the container also stores a *clone* (a copy) of your repository in its own a file system stored in and accessed by the container. You have complete rein over this VM. You can log into it by simply opening a Terminal in VSCode. The clone of your repo is in the /workspaces folder within the container file system (or storage *volume*, as it's called).

It is very important to understand that if you delete the container or its storage volume (which you can in principle do through Docker Desktop), this will erase all the work you have stored in the container. To make your changes persistent, you must (1) stage, (2) commit, and (3) push your container-local changes to your repository on GitHub. We'll show you how to do that separately.

(*) Why? Some required Docker functions are not yet implemented for Docker running on Linux hosts.
