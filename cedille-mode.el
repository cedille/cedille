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

;;; stlc-mode.el --- Major mode for Stlc

;;; Commentary:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Dependency

;;; Code:

(require 'quail)

(require 'se-mode)
(eval-when-compile (require 'se-macros))

(defvar cedille-version "0.1"
  "The version of the cedille mode.")

(defvar cedille-program-name "cedille"
  "Program to run for cedille mode.")

(se-create-mode "Cedille" nil
  "Major mode for Cedille files."

  (setq-local comment-start "%")
  
  (se-inf-start
   (or (get-buffer-process "*cedille-mode*") ;; reuse if existing process
       (start-process "cedille-mode" "*cedille-mode*" cedille-program-name))))

(modify-coding-system-alist 'file "\\.ced\\'" 'utf-8)

(quail-define-package "Cedille" "UTF-8" "δ" t ; guidance
		      "Cedille input method."
		      nil nil nil nil nil nil t) ; maximum-shortest

(set-input-method "Cedille")
(mapc (lambda (pair) (quail-defrule (car pair) (cadr pair) "Cedille"))
	'(("\\l" "λ") ("\\>" "→") ("\\r" "→") ("\\a" "∀") ("\\B" "□") ("\\P" "Π") 
          ("\\t" "★") ("\\o" "☆") ("\\." "·") ("\\f" "⇐") ("\\u" "↑") 
          ("\\h" "●") ("\\c" "χ")))

(provide 'cedille-mode)
;;; cedille-mode.el ends here

