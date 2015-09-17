;;; cedille-mode.el --- Major mode for Cedille
;;;
;;; Add something like the following to your .emacs file to load this
;;; mode for .ced files:
;;;
;;;   (autoload 'cedille-mode "cedille-mode" "Major mode for editing cedille files ." t)
;;;   (add-to-list 'auto-mode-alist '("\\.ced\\'" . cedille-mode))
;;;
;;; You will need to link or copy this file to a load directory for emacs.
;;; I have this in my .emacs file to make ~/.emacs.d such a directory:
;;;
;;;   (add-to-list 'load-path "/home/astump/.emacs.d/")
;;;
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Dependency


;;; Code:

(defvar cedille-version "0.1"
  "The version of the cedille mode.")

(require 'quail)

(setq auto-mode-alist (cons (cons "\\.ced\\'" 'cedille-mode) auto-mode-alist))

(modify-coding-system-alist 'file "\\.ced\\'" 'utf-8)

(with-temp-buffer
    (quail-define-package "Cedille" "UTF-8" "δ" t ; guidance
     "Cedille input method."
     nil nil nil nil nil nil t ; maximum-shortest
     ))

(eval `(define-derived-mode cedille-mode
  ,(if (fboundp 'prog-mode) 'prog-mode)
  "Cedille"
  "Major mode for Cedille files."

 (set-input-method "Cedille")
 (mapc (lambda (pair) (quail-defrule (car pair) (cadr pair) "Cedille"))
	'(("\\l" "λ") ("\\>" "→") ("\\r" "→") ("\\R" "⇒") ("\\a" "∀") ("\\m" "✓") ("\\B" "□") ("\\P" "Π") ("\\i" "ι") 
          ("\\t" "★") ("\\o" "☆") ("\\." "·") ("\\x" "ξ") ("\\f" "⇐") ("\\s" "∈") ("\\n" "ν") ("\\u" "↑") ("\\U" "𝓤") ("\\:" "∷")
          ("\\e" "η") ("\\h" "●") ("\\k" "𝒌") ("\\c" "χ") ("\\b" "β") ("\\d" "δ") ("\\z" "ζ") ("\\<" "〈")("\\>" "〉")))
))

(provide 'cedille-mode)
;;; cedille-mode.el ends here
