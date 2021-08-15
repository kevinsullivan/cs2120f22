# Copyright 2021 Rector and Visitors of the University of Virginia.
# Author: Kevin Sullivan, UVA CS Department, sullivan@virginia.edu.

# Boot Up

- Update your operating system
  - Windows: You must update to Windows 10 Education
  - OSX: You must update to the lastest version of OSX
- Install Git on your computer
  - Install from _____
  - Configure user.name and user.email globally
  - If you're on OSX, install Git Credential Manager Core 
    - https://github.com/microsoft/Git-Credential-Manager-Core/releases/download/v2.0.498/gcmcore-osx-2.0.498.54650.pkg
    - git-credential-manager-core
- Install Docker Desktop on your computer (Windows, OSX)
- Install VSCode on your computer
- Fork this repository into your GitHub account 
  - Create a GitHub account for yourself if you don't already have one
  - Log in to your GitHubAccount
  - etc ______
- Clone your fork of our repo to a local directory ("dir") on your computer
  - Visit your forked repo
  - Select Code, etc ________
  - Open a terminal on your local machine and git clone https://...______
- Run VSCode to open that directory (e.g., 
  - cd into new directory
  - launch VSCode and have it open the current directory
  - ``` sh
    code .
    ```
- Now the automated Docker container build process should kick off. Click link for details.
- When it's done, open a terminal in VSCode. It should now be a terminal into the container.
- NB: Any changes you commit now go into a copy of your repo inside the container
- Run leanproject build in the top-level directory using this terminal.
- Confirm that test file in the test directory works as indicated by the comments inside
- If not, debug or ask for help. If so, have fun! Are there any other possibilities?

Push frequently to GitHub to backup containerized working repo to their remote computer
