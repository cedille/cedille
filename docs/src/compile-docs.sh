#!/bin/bash
# to be run in docs/src/ because of the relative path

makeinfo -o ../info/cedille-info-main.info cedille-info-main.texi

# for later, generating more forms of the documentation
# makeinfo -o ../html --html cedille-main.texi
# texi2pdf -o ../pdf/Cedille-info-main.pdf cedille-main.texi
