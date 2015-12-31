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

; set in .emacs file
(defvar cedille-program-name "cedille-executable"
  "Program to run for cedille mode.")

(defvar cedille-info-buffer-trailing-edge 1 "Number of blank lines to insert at the bottom of the info buffer.")

(defun cedille-info-buffer-name() (concat "*cedille-info-" (file-name-base (buffer-name)) "*"))

(defun cedille-info-buffer()
  (let* ((n (cedille-info-buffer-name))
         (b (get-buffer-create n)))
    (with-current-buffer b
       (setq buffer-read-only nil))
    b))

(defun cedille-adjust-info-window-size()
  (let ((w (get-buffer-window (cedille-info-buffer))))
   (when w
     (fit-window-to-buffer w)
     (window-resize w cedille-info-buffer-trailing-edge))))

(defun cedille-mode-inspect ()
  "Displays information on the currently selected node in the *cedille* buffer."
  (interactive)
  (let ((b (cedille-info-buffer))
        (txt (if se-mode-selected
               (se-mode-pretty-json (se-term-to-json (se-mode-selected)))
               "\n")))
    (with-current-buffer b (erase-buffer) (insert txt) (setq buffer-read-only t))
    (cedille-adjust-info-window-size)
    (setq deactivate-mark nil)))

(defun se-mode-goto-first-child()
  (let* ((outer (se-find-point (point) se-mode-parse-tree))
         (kids (se-node-children outer))
         (term (if (null kids) outer (car kids))))
        (goto-char (se-term-start term))))

(defun se-mode-select-first-child()
  "Selects the first child of the smallest span around point."
  (interactive)
  (se-mode-goto-first-child)
  (se-mode-expand-selected))

(defun se-mode-select-first-child-if()
  "Marks the first child of the smallest span around point."
  (interactive)
  (se-mode-shrink-selected)
  ; if shrinking the selected region results in no region's being selected, it is time to find the first child
  (unless se-mode-selected
     (se-mode-select-first-child)))

(defun se-mode-select-last-helper (prev)
  (let ((next (se-mode-next)))
    (if (null next) prev
      (se-mode-select next)
      (se-mode-select-last-helper next))))
  
(defun se-mode-select-last()
  "Selects the last sibling of the parent of the current node."
  (interactive)
  (se-mode-select-last-helper (se-mode-selected)))

(defun se-mode-select-first-helper (next)
  (let ((prev (se-mode-previous)))
    (if (null prev) next
      (se-mode-select prev)
      (se-mode-select-first-helper prev))))
  
(defun se-mode-select-first()
  "Selects the first sibling of the parent of the current node."
  (interactive)
  (se-mode-select-first-helper (se-mode-selected)))

(defun cedille-mode-select-next()
  "Selects the next sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-next)
  (cedille-mode-inspect))

(defun cedille-mode-select-previous()
  "Selects the previous sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-previous)
  (cedille-mode-inspect))

(defun cedille-mode-select-parent()
  "Selects the parent of the currently selected node in 
the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-expand-selected)
  (cedille-mode-inspect))

(defun cedille-mode-select-first-child()
  "Selects the first child of the lowest node in the parse tree
containing point, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-first-child-if)
  (cedille-mode-inspect))

(defun cedille-mode-select-first()
  "Selects the first sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-first)
  (cedille-mode-inspect))

(defun cedille-mode-select-last()
  "Selects the last sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-last)
  (cedille-mode-inspect))

(defun cedille-mode-toggle-info()
  "Shows or hides the Cedille info buffer."
  (interactive)
  (let* ((b (cedille-info-buffer))
         (w (get-buffer-window b)))
    (if w (delete-window w) (display-buffer b) (cedille-adjust-info-window-size))))

; se-navi-define-key maintains an association with the major mode,
; so that different major modes using se-navi-define-key can have
; separate keymaps.
(defun cedille-modify-keymap()
  (se-navi-define-key 'cedille-mode (kbd "f") #'cedille-mode-select-next)
  (se-navi-define-key 'cedille-mode (kbd "b") #'cedille-mode-select-previous)
  (se-navi-define-key 'cedille-mode (kbd "p") #'cedille-mode-select-parent)
  (se-navi-define-key 'cedille-mode (kbd "n") #'cedille-mode-select-first-child)
  (se-navi-define-key 'cedille-mode (kbd "g") #'se-mode-clear-selected)
  (se-navi-define-key 'cedille-mode (kbd "\C-g") #'se-navigation-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "e") #'cedille-mode-select-last)
  (se-navi-define-key 'cedille-mode (kbd "a") #'cedille-mode-select-first)
  (se-navi-define-key 'cedille-mode (kbd "i") #'cedille-mode-toggle-info)
  (se-navi-define-key 'cedille-mode (kbd "s") nil)
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

