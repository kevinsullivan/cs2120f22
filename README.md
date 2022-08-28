# CS2120-003 Fall 2021

Welcome to UVa CS2120 Fall 2022 taught by Kevin Sullivan. We're going to use some software this term, which we've packaged up for you into what we hope and expect will be an easy install. You must provide both VSCode and Docker Desktop on your Windows or MacOS computer. We then provide our Discrete Mathematics Development Environment based on VSCode. 

There is mixed news for Windows 10 *Home* users: in our experience, Docker Deskop seems to still not to run properly on  Windows 10 *Home*. You might well still be using Windows 10 Home if you're using an older laptop. In this case, you'll need to obtain an upgrade key to update to Windows 10 Professional or Education mor to Windows 11. At UVa this is free and easy. Everything is desribed in detail next. 

## Detailed installation instructions

- Update your operating system:
  - If MacOS: Be sure your OS is up-to-date (current version of Monterey, 12.5.2 as of this writing).
  - If Windows:
    - If you already have Windows Pro, Education, Enterprise, or Windows 11, skip the remaining steps, else continue.
    - Windows 10 Home won't do: You must update to Windows 10 Professional, Enterprises, or Education
      - Outside UVa:  Update keys are readily and immediately available online
      - UVa students: Get or update to Windows 10 Education through ITS, as follows:
        1. Get OS Windows Update license key from ITS: <https://azureforeducation.microsoft.com/devtools>.
        3. Sign in using your UVa credentials.
        4. Click Software in the left-hand navigation. 
        5. Select Windows 11 Education then click on the right to get an update key. Copy the key to your clipboard.
        6. After obtaining the OS key copy it, go to Windows Activation Settings, select Change Product Key, paste your upgrade key, commit the change (hit Enter or OK or whatever is required). Reboot your machine. When it boots up, you can check the *System Information* App to confirm that your OS is updated.
- Install git on your computer (if you know you already have it, skip this step):
  - Windows: https://git-scm.com/download/win
  - OSX/MacOs
    - Find and run the Terminal program
    - Enter the following command in the window: xcode-select --install
    - When it asks, go ahead with the standard install process. 
- Have a GitHub account. Create one for yourself if necessary. It's free: <https://github.com/>
- Install Docker Desktop: <https://www.docker.com/products/docker-desktop>. It's free. If you already have it, update it to the current version.
- Install VSCode: <https://code.visualstudio.com/download>. It's free.
- Launch Docker Desktop and watch for it to complete its start-up procedures. While it starts up, continue to the remaining instructions that follow here.
- Use GitHub to fork this repository now. How? Here:
  - Be logged in to your GitHub account.
  - Visit *this* repository on GitHub (which is probably where you're reading this) while logged in to your GitHub account.
  - "Fork" this repo using the *Fork* button in the upper right corner. This will create a clone of this repository (a copy that remembers where it came from) under your GitHub account. 
  - Visit your GitHub web page to confirm that you now own a clone of this repository. Click to view the repository.
  - Select the green Code button, then HTTPS, then copy the URL that is provided. This will be the GitHub URL of your newly forked copy of the respository.
- Start up your new environment
  - Start a *new* VSCode window.
  - Using the "extensions" tool (four squares with one out of place on the left of your VSCode screen), search for and install the *Remote Containers* extension. (The green icon at the lower left gets you the available Remote Containers commands direclty.)
  - Use CTRL/CMD-SHIFT-P to bring up the VSCode command palatte.
  - Search for and select *Clone Repository in Container Volume*
  - Paste in the GitHub URL of your new clone as the argument.
  - If you're asked to choose something, select *unique repository*.
- Now wait while your environment is built. You can click the *Starting Dev Container* link in the lower right to see the build process if you want. Wait for the building activity to end and for your environment to "boot up" before taking any further actions. There is a status bar at the bottom of the screen that reflects build processes status and activities.
- Check to see that everything is working
  - Open the lean_test.lean file (src/test/leantest.lean) and check that the conditions described therein are satisfied.
  - Open the python_test.py file (src/test/hello.lean), check for an arrown in the upper right to run the HelloWorld program, and run it. 
- Configure git on your new containerized operating system
  - Open a new Terminal window in VSCode
  - Issue the following commands, filling in your details as appropriate
    - git config --global user.name "Your Name Here"
    - git config --global user.email "your@email.here"
- You may now work in and exit from VSCode as you wish. VSCode will let you re-open this project when you're ready to work on it again.

You now have, up and running, a nice discrete math development environment ever. You're done here now!

## If you find a problem or an opportunity

If you think you've found a problem, revisit this GitHub page and report an Issue. Better yet, if you then fix the problem on your own clone of this site, commit and push it to your GitHub repo then send us a *Pull Request*. That will will send us your changes to review and possibly merge them into our main repository, whereupon they will then become available for anyone else to *Pull*, as well.  

## Legal and contact

- Acknowledgement: This work is supported in part by the National Science Foundation under grant (Award Abstract) #1909414 to Kevin Sullivan and Sebastian Elbaum.
- Copyright: © 2021-2022 by Kevin Sullivan, et al.
- Primary and Contact Author: Kevin Sullivan. UVa CS Dept. sullivan@virginia.edu. 
