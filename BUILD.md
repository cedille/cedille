# Building Cedille version 1.0

0. Install Agda version 2.5.4 or above, which is needed to compile Cedille.
   Please note that Cedille currently does not work on Windows, only Linux and
   Mac (though Windows support should be available soon).

1. Clone a copy of the Iowa Agda Library (probably best to do this
   in some other directory), and check out version 1.5:

   * `git clone https://github.com/cedille/ial.git`
   * `cd ial`
   * `git checkout v1.5.0`

   For SVN users, the (soon to be deprecated) repo can be accessed by:

   `svn co https://svn.divms.uiowa.edu/repos/clc/projects/agda/ial`

2. Create a symbolic link in the Cedille directory, pointing to the
   IAL directory.  The link should be named `ial`.

4. Now you can run `make` in the Cedille directory, and this should
   compile the cedille executable (which should appear in the Cedille
   directory).

5. Follow the directions at the top of cedille-mode.el in the Cedille
   directory, to set up Cedille mode within emacs.  Then you can open
   files like `lib/bool.ced` within emacs and hit "Meta-s" to process
   them (if all goes well, the mode should change to "Cedille navi"
   and you can then type "h" for help).

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
