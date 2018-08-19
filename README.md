# Çedille
The Cedille programming language empowers you with the ability to
interactively prove mathematical theorems as well as verify
programs. Using the Cedille Emacs mode you interact directly with the
compiler to check your syntax, elegantly navigate through parts your
code, obtain rich contextual information about those portions of code,
and of course receive useful feedback about the
correctness/non-correctness of that code. The Cedille compiler paired
with the Emacs mode comprises a fully featured interactive theorem
prover, but you can also compile your Cedille code into
[Racket](https://racket-lang.org/) in order to execute your code.

Beyond its next-generation Emacs interface, the Cedille programming
language embodies an innovative impredicative dependent type theory
that permits a much smaller trusted computing base than some other
interactive theorem provers. In particular, the theory behind Cedille
enables one to derive an induction principle of a lambda encoded
datatype, so that it is not necessary to extend the core theory to
support inductive datatypes.

## Releases
The Cedille compiler is currently maintained at
[github.com/cedille/cedille](https://github.com/cedille/cedille),
and you can download current and past releases on the
[github release page](https://github.com/cedille/cedille/releases).

The version number of each Cedille release follows the
[semantic versioning standard](https://semver.org/),
so that the first number conveys the major version (generally, an
introduction of backwards incompatible changes triggers a change in
this number), the second number conveys the minor version
(introduction of significant but backwards compatible changes), and
the third number conveys the patch level (mainly for bug fixes).

## Installation
See INSTALL.txt

## Documentation
See the info file at
[docs/info/cedille-info-main.info](https://github.com/cedille/cedille/blob/master/docs/info/cedille-info-main.info).
Alternatively, while in Cedille mode in Emacs, enter Cedille
navigation mode by pressing `M-s` and then press `h`. This will bring
up the info file within Emacs.

## License
TODO
