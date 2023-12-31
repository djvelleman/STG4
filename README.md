# STG4

This is the *Set Theory Game*. It uses the [Lean4 Game Engine](https://github.com/leanprover-community/lean4game) and it is hosted at [adam.math.hhu.de](https://adam.math.hhu.de).

## Getting Started

There are multiple ways to run the game while developing it:

### VSCode Devcontainer

The full instructions are at [Running games locally](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#running-games-locally).
In particular, the recommended setup is to have `docker` installed on your computer
and then click on the pop-up "Reopen in Container" which is shown when
opening this project in VSCode.

You can then open [localhost:3000](http://localhost:3000) in a browser.

After making changes to the code, you need to run `lake build` in a terminal and
reload the web page inside the "Simple Browser".

### Codespaces

You can work on it using Github codespaces (click "Code" and then "Codespaces" and then "create codespace on main"). It it should run the game locally in the background. You can open it for for example under "Ports" and clicking on
"Open in Browser".

Note: You have to wait until `npm` started properly.
In particular, this is after a message like
`[client] webpack 5.81.0 compiled successfully in 38119 ms` appears in the terminal, which might take a good while.

As with devcontainers, you need to run `lake build` after changing any lean files and then reload the browser.

### Local setup

The full instructions are at [Running games locally](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#running-games-locally).
In particular, the recommended setup is to have `docker` installed on your computer
and then click on the pop-up "Reopen in Container" which is shown when
opening this project in VSCode.

The game is then accessible at [localhost:3000/#/g/local/game](http://localhost:3000/#/g/local/game).

### Gitpod

You can work on this repository using Gitpod : [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/hhu-adam/NNG4)

Note that gitpod is *not* setup to start the game in the background to play.


## Creating a new game

In order to create a new game, click "use this template"  above to create your own game. That way there is a github action that can build a docker image from your `main` branch which can be used to add the game to the server at [adam.math.hhu.de](https://adam.math.hhu.de).
