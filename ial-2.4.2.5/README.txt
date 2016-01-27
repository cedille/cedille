The Iowa Agda Library (IAL)
Aaron Stump

1. About the library

The goal is to provide a concrete library focused on verification
examples, as opposed to mathematics.  The library has a good number
of theorems for booleans, natural numbers, and lists.  It also has
trees, tries, vectors, and rudimentary IO.  A number of good ideas
come from Agda's standard library.

2. Using the library 

This library is known to work with Agda 2.4.2.3/2.4.2.2/2.4.2.1.

In Agda, you can include the whole library by importing lib.agda.  

You can compile the whole library by running "make".

The library is set up so there are no name conflicts between modules
(except sometimes I have several versions of the same module, like
stream and stream2 or nat-division and nat-division2, and there might
be name conflicts in such cases).

3. Browsing the library

You can get some overview of what is in the library by following
imports from lib.agda (this is the main entry point for the library).

4. Credits

The library is mostly written by myself, but it also includes some
contributions from John Bodeen, Harley Eades, and undergraduates who
took my Programming Language Concepts class, Spring 2014 and 2015,
especially Tom Werner.

5. Releases

Released versions of the library can be found at

https://svn.divms.uiowa.edu/repos/clc/projects/agda/ial-releases

The development version is at

https://svn.divms.uiowa.edu/repos/clc/projects/agda/ial

6. License

This library is currently provided under the MIT License, see LICENSE.txt.

7. Documentation

There is no formal documentation currently, besides comments in the files.

Much of the library is described in my book, "Verified Functional
Programming in Agda", to be published 2016 with ACM Books.

