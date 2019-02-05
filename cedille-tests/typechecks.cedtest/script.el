
(cedille-test-perform-key-events " ") ; Add input so this doesn't get executed right after parsing and before the parse tree is assembled (probably should change cedille-mode-tests.el)

(setq output (if cedille-mode-error-spans "Error" "Checks"))
