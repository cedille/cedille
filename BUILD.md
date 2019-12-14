# Building Cedille version 1.1.2 with Stack

1. Install C libraries *zlib** and *ncurses** for building Agda
    - `apt install zlib1g-dev libncurses5-dev` on Ubuntu for example
    - On MacOS these may already be available if you have xcode libraries installed
2. In the Cedille repository directory:
    - Run `stack build Agda alex happy`
    - Run `stack build --copy-bins --local-bin-path .`
3. Add the following to your `~/.emacs` file, changing the path to match your system
```
(setq cedille-path "/path/to/cedille-dir/")
(add-to-list 'load-path cedille-path)
(require 'cedille-mode)
```

# Editing Agda Source Files for Cedille

 * Since Agda 2.5.4 now uses a library system, you need to tell Agda
   about the three libraries used for Cedille (these are for the Cedille
   sources, the IAL, and some stuff for the parser).  If you run `make`
   (or directly `./create-libraries.sh`) it will create the libraries
   file with the full paths to these libraries.  Then you can add an
   Agda2 program argument (via customize-group then "agda2" in emacs)
   to reference the libraries file with
   `--library-file=<path-to-your-generate-libraries-file>`.

 * Warning: you should compile Cedille to an executable using `make`,
   rather than from within Agda in Emacs.  Or else please look at 
   `Makefile` for extra arguments you have to give to Agda
   when compiling Cedille.
