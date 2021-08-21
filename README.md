# Create a Lean IDE using VSCode Remote Containers

The purpose of this document is to guide you through the process of setting up a VSCode-based development environment for writing and analyzing logic and mathematics using the Lean Prover. To use this solution, you must be running a computer that runs either the Windows 10 Professional or Enterprise or Education, or MacOS, operating system. For University of Virginia students, see below for instructions on updating your Windows 10 Home computer to use Windows 10 Education. Here are the steps that you should be able to follow to create your own, GitHub-backed up-and-running project using the Lean Prover (Community) and mathlib. 

- Update your operating system:
  - If MacOS: Be sure your OS is completely up-to-date (current version of Big Sur, currently 11.5.1 as of this writing).
  - If Windows 10 Home: Update to Windows 10 Education (Windows 10 Home won't do). If you're a UVa student, updating to Windows 10 Education is free.
    1. Get OS Windows Update license key from ITS: https://virginia.service-now.com/its/.  
    2. Click Software in the left-hand navigation. Select the *latest* Windows 10 Education version. Get an update key.
    3. After obtaining the OS key, copy and paste it in to the Windows Activation page (same screen as Windows Update).
    4. Reboot your machine. You can check the Windows *System Information* app to confirm that your OS is updated.
- Have a GitHub account. Create one for yourself if necessary. It's free: https://github.com/
- Install Docker Desktop: https://www.docker.com/products/docker-desktop.
- Install VSCode: https://code.visualstudio.com/download.
- Launch Docker Desktop and watch for it to complete its start-up procedures. While it starts up, continue on to the remaining instructions. 
- Use GitHub to fork this repository now. 
  - Be logged in to your GitHub account.
  - Visit this very repository on GitHub (which is probably where you're reading this)
  - Fork this repo using the *Fork* button in the upper right corner. 
  -   This will create a copy of this entire repository in *your* GitHub account. Visit your GitHub page to confirm that you now have a clone of this repository. 
  -   Select the green Code button, then HTTPS, then copy the URL that is provided. This will be the GitHub URL of your newly forked copy of the respository.
- Open our Lean Development Environment directly from your new GitHub repository
  - Launch a *new* VSCode window. 
  - Use CTRL/CMD-SHIFT-P to bring up the VSCode command palatte. 
  - Search for and select *Clone Repository in Container Volume*
  - Paste the URL of your new repository as the argument.
  - If it asks, select *unique repository*.
- Wait for your development environment to completely "boot up" before taking any further actions.
- Check to see that everything is working
  - Open the test.lean file (src/test/test_lean_mathlib.lean)
  -Check that the conditions described therein are satisfied.

What you now have is a complete VSCode-based interactive development environment for using the Lean Prover and its math library. This development environment is provided by a *Docker container* running Linux (Ubuntu 20.04 LTS) configured with all the necessary software. You should not have to install any software beyond Docker Desktop and VSCode on your host (laptop) computer. In addition to running our Linux OS, the container also stores a *clone* (a copy) of your repository in its own a file system stored in and accessed by the container. You have complete rein over this VM (Virtual Machine). You can log into it by simply opening a Terminal in VSCode. The clone of your repo is in the /workspaces folder within the container file system (or storage *volume*, as it's called).

It is very important to understand that if you delete the container or its storage volume (which you can in principle do through Docker Desktop), this will erase all the work you have stored in the container. To make your changes persistent, you must (1) stage, (2) commit, and (3) push your container-local changes to your repository on GitHub. We'll show you how to do that separately.

(*) Why? Some required Docker functions are not yet implemented for Docker running on Linux hosts.
