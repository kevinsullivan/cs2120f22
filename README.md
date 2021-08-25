# CS2120-003 Fall 2021

Welcome to UVa CS2120-003 Fall 2021 taught by Kevin Sullivan. We're going to use some software this term, which we've packaged up for you into what we hope and expect will be a very easy install.You must first provide both VSCode and Docker Desktop running properly on a Windows 10 or MacOS computer. We then provide our Mathematics Development Environment, based on VSCode, the "Lean Prover" and its library of formalized mathematics, and your own GitHub repository. We'll explain that if you're not sure what it means. Slightly mixed news for Windows 10 *Home* users: Docker Deskop seems to still have properly on a Windows 10 *Home* computer. In this case, you'll need to obtain an upgrade key to update to Windows 10 Professional or Education. At UVa this is free and easy. Everything is desribed in detail next. Now just follow the yellow brick road .,..,.

## .,,.. the Yellow Brick Road

- Update your operating system:
  - If MacOS: Be sure your OS is up-to-date (current version of Big Sur, 11.5.2 as of this writing).
  - If Windows:
    - Windows 10 Home won't do, but it's probably what you have. Run the System Information App to find out.
    - You must either be running or update to Windows 10 Professional, Enterprises, or Education
      - Outside UVa:  Update keys are readily available online
      - UVa students: Get or update to Windows 10 Education through ITS, as follows:
        1. Get OS Windows Update license key from ITS: <https://virginia.service-now.com/its/>.  
        2. Click Software in the left-hand navigation. Select the *latest* Windows 10 Education version. Get an update key.
        3. After obtaining the OS key, copy and paste it in to the Windows Activation page (same screen as Windows Update).
        4. Reboot your machine. You can check the Windows *System Information* app to confirm that your OS is updated.
- Have a GitHub account. Create one for yourself if necessary. It's free: <https://github.com/>
- Install Docker Desktop: <https://www.docker.com/products/docker-desktop>. It's free. If you already have it, update it to the current version.
- Install VSCode: <https://code.visualstudio.com/download>. It's free.
- Launch Docker Desktop and watch for it to complete its start-up procedures. While it starts up, continue to the remaining instructions that follow here.
- Use GitHub to fork this repository now. How? Here:
  - Be logged in to your GitHub account.
  - Visit *this* repository on GitHub (which is probably where you're reading this) while logged in to your GitHub account.
  - "Fork" this repo using the *Fork* button in the upper right corner. This will create a clone of this repository (a copy that remembers where it came from) under your GitHub account. We recommend that you should change the name of your GitHub repo (hit the pencil icon next to its name on GitHub to start editing it) to reflect the nature of your project. Doing this will avoid conflicts should you try to do this procedure again.
  - Visit your GitHub web page to confirm that you now own a clone of this repository. Click to view the repository.
  - Select the green Code button, then HTTPS, then copy the URL that is provided. This will be the GitHub URL of your newly forked copy of the respository.
- Start up your new environment
  - Start a *new* VSCode window.
  - Use CTRL/CMD-SHIFT-P to bring up the VSCode command palatte.
  - Search for and select *Clone Repository in Container Volume*
  - Paste in the GitHub URL of your new clone as the argument.
  - If you're asked to choose something, select *unique repository*.
- Now wait while your environment is built. You can click in the lower right to see the build process if you want. Wait for the building activity to end and for your environment to "boot up" before taking any further actions. There is a status bar at the bottom of the screen that reflects build processes status and activities.
- Check to see that everything is working
  - Open the test.lean file (src/test/test_lean_mathlib.lean)
  - Check that the conditions described therein are satisfied.
- Configure git on your new containerized operating system
  - Open a new Terminal window in VSCode
  - Issue the following commands, filling in your details as appropriate
    - git config --global user.name "Your Name Here"
    - git config --global user.email "your@email.here"
- You may now work in and exit from VSCode as you wish. VSCode will let you re-open this project when you're ready to work on it again.

You now have, up and running, the coolest mathematical development environment ever. You're done here now!

## Of course, if your're curious

- Yep, that was clickbait, but hey, your new environment delivers many capabilities. They include the following.
  - VSCode will be open and ready for you to start developing your applications with professional-quality infrastructure
  - A containerized/virtual computer delivering a richly configured environment including the Lean Prover and its library of formalized mathematics (mathlib)
    - Ubuntu 20.04 LTS operating system
    - Lean Prover Community, with mathlib
    - Widely used VSCode IDE
    - Root "shell" into Ubuntu container.
    - VSCode operates on a clone of your repo created in your container
  - The entire development environment builds itself when you first follow these procedures
- The clone of your repo is in the directory, /workspaces, in the container.

## If you find a problem or an opportunity

If you think you've found a problem, revisit this GitHub page and report an Issue. Better yet, if you then fix the problem on your own clone of this site, commit and push it to your GitHub repo then send us a *Pull Request*. That will will send us your changes to review and possibly merge them into our main repository, whereupon they will then become available for anyone else to *Pull*, as well.  

## Legal and contact

- Acknowledgement: This work is supported in part by the National Science Foundation under grant (Award Abstract) #1909414 to Kevin Sullivan and Sebastian Elbaum.
- Copyright: © 2021 by Kevin Sullivan, Sebastian Elbaum, et al.
- Primary and Contact Author: Kevin Sullivan. UVa CS Dept. sullivan@virginia.edu. Acknowledgements to Charlie Houghton, Andrew Elsey, et al.  
