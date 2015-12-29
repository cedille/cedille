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

(defun cedille-modify-keymap()
  (define-key se-navigation-mode-map (kbd "f") #'se-mode-select-next)
  (define-key se-navigation-mode-map (kbd "b") #'se-mode-select-previous)
  (define-key se-navigation-mode-map (kbd "p") #'se-mode-expand-selected)
  (define-key se-navigation-mode-map (kbd "n") #'se-mode-shrink-selected)
  (define-key se-navigation-mode-map (kbd "e") nil)
  (define-key se-navigation-mode-map (kbd "s") nil)
)

(cedille-modify-keymap)

;(add-hook 'se-navigation-mode-hook 'cedille-modify-keymap)
;(eval-after-load 'se-navi 'cedille-modify-keymap)

(se-create-mode "Cedille" nil
  "Major mode for Cedille files."

  (setq-local comment-start "%")
  
  (se-inf-start
   (or (get-buffer-process "*cedille-mode*") ;; reuse if existing process
       (start-process "cedille-mode" "*cedille-mode*" cedille-program-name)))

  (set-input-method "Cedille")
)

(modify-coding-system-alist 'file "\\.ced\\'" 'utf-8)

(quail-define-package "Cedille" "UTF-8" "δ" t ; guidance
		      "Cedille input method."
		      nil nil nil nil nil nil t) ; maximum-shortest

(mapc (lambda (pair) (quail-defrule (car pair) (cadr pair) "Cedille"))
	'(("\\l" "λ") ("\\L" "Λ") ("\\>" "→") ("\\r" "→") ("\\a" "∀") ("\\B" "□") ("\\P" "Π") 
          ("\\t" "★") ("\\o" "☆") ("\\." "·") ("\\f" "⇐") ("\\u" "↑") 
          ("\\h" "●") ("\\c" "χ") ("\\k" "𝒌")))

(provide 'cedille-mode)
;;; cedille-mode.el ends here

