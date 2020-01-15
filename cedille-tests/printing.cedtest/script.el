

(cedille-test-perform-key-events "p" "n" "f" "n" "f")

(cedille-copy-inspect-buffer-to-scratch-buffer)

(cedille-test-perform-key-events "p" "f" "n" "f")

(cedille-copy-inspect-buffer-to-scratch-buffer)

; go to the scratch buffer, so we can get the output of all the tests above

(cedille-test-perform-key-events "X")

(setq output (buffer-string))
