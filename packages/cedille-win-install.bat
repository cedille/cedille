@echo off
rem Set the window's title
title Installing Cedille
rem Set what directory to install cedille to
set cedille-dir=%programfiles%\cedille
rem Create the cedille directory, and its subdirectories
md "%cedille-dir%"
md "%cedille-dir%\cedille-mode\"
md "%cedille-dir%\se-mode\"
md "%cedille-dir%\bin\"
rem Copy files to the new cedille directory
copy "cedille.exe" "%cedille-dir%\bin"
copy "cedille-mode.el" "%cedille-dir%"
copy "cedille-mode" "%cedille-dir%\cedille-mode"
copy "se-mode" "%cedille-dir%\se-mode"
copy "cedille-info-main.info" "%cedille-dir%\cedille-info-main.info"
copy "copyright" "%cedille-dir%"
rem Add the cedille directory to PATH, if it isn't already there
echo %path%|find /i "%cedille-dir%\bin">nul || setx path "%path%;%cedille-dir%\bin"
rem Add cedille-mode.el to the EMACSLOADPATH, if it isn't already there
echo %emacsloadpath%|find /i "%cedille-dir%\">nul || setx emacsloadpath "%cedille-dir%\;%emacsloadpath%"
rem Print finish message
echo Cedille installed
