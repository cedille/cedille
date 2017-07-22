;;;;INSPECT MODE
;;; This document contains code related to cedille inspect mode.
;;; This mode, called using the hotkey 'i', provides information about the selected span

;;TODO - make sure upon opening inspect mode that it goes to position 1

;(require 'se-mode)

(load-library "cedille-mode-parent")


(define-minor-mode cedille-inspect-view-mode
  "Creates inspect mode, which displays information about the current node"
  nil         ; init-value, whether the mode is on automatically after definition
  " Context"  ; indicator for mode line
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap) ; inherit bindings from parent keymap
    (define-key map (kbd "i") #'cedille-mode-close-active-window) ; exit inspect mode
    (define-key map (kbd "I") #'cedille-mode-close-active-window) ; exit inspect mode
    map))

(defun cedille-mode-inspect-buffer-name() (concat "*cedille-inspect-" (file-name-base (buffer-name)) "*"))

(defun cedille-mode-inspect-buffer()
  (get-buffer-create (cedille-mode-inspect-buffer-name)))
  ;(let* ((n (cedille-mode-inspect-buffer-name))
  ;       (b (get-buffer-create n)))
  ;  b))

(defun cedille-mode-inspect ()
  "Displays information on the currently selected node in 
the info buffer for the file.  Return the info buffer as a convenience."
  (when se-mode-selected
    (let* ((span (se-mode-selected))
	   (buffer (cedille-mode-inspect-buffer))
           (d (se-term-to-json span))
           (txt (se-mode-pretty-json-interactive (if cedille-mode-debug d (cedille-mode-filter-out-special d)))))
      (with-current-buffer buffer
	(setq buffer-read-only nil)
	(cedille-inspect-view-mode)
	(erase-buffer)
	(insert txt)
	(goto-char 1)
	(setq buffer-read-only t))
      (cedille-mode-rebalance-windows)
      (setq deactivate-mark nil)
      buffer)))

(defun cedille-mode-inspect-clear-all ()
  (interactive)
  (se-pin-clear-all 'se-interactive)
  (se-mapc 'se-inf-clear-span-interactive (se-mode-parse-tree))
  (cedille-mode-inspect))

(defun cedille-mode-inspect-clear ()
  (interactive)
  (when se-mode-selected
    (setq span (se-first-span (se-mode-selected)))
    (setq s (se-span-start span))
    (setq e (se-span-end span))
    (se-unpin-list (se-pins-at s e 'se-interactive))
    (se-inf-clear-span-interactive span))
  (cedille-mode-inspect))

(provide 'cedille-mode-inspect)
