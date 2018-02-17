;;;;INSPECT MODE
;;; This document contains code related to cedille inspect mode.
;;; This mode, called using the hotkey 'i', provides information about the selected span

;;TODO - make sure upon opening inspect mode that it goes to position 1

(define-minor-mode cedille-inspect-view-mode
  "Creates inspect mode, which displays information about the current node"
  nil         ; init-value, whether the mode is on automatically after definition
  " Context"  ; indicator for mode line
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap) ; inherit bindings from parent keymap
    (define-key map (kbd "i") #'cedille-mode-close-active-window) ; exit inspect mode
    (define-key map (kbd "I") #'cedille-mode-close-active-window) ; exit inspect mode
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "inspect mode"))
    map))

(defun cedille-mode-inspect-buffer-name () (concat "*cedille-inspect-" (file-name-base) "*"))

(defun cedille-mode-inspect-buffer ()
  (get-buffer-create (cedille-mode-inspect-buffer-name)))

(defun cedille-mode-inspect ()
  "Displays information on the currently selected node in 
the info buffer for the file.  Return the info buffer as a convenience."
  (when se-mode-selected
    (let* ((parent cedille-mode-parent-buffer)
           (span (se-mode-selected))
	   (buffer (cedille-mode-inspect-buffer))
           (d (se-term-to-json span))
           (txt (se-mode-pretty-json-interactive (if cedille-mode-debug d (cedille-mode-filter-out-special d)))))
      (with-current-buffer buffer
	(setq buffer-read-only nil
	      window-size-fixed nil
              cedille-mode-parent-buffer parent)
	(cedille-inspect-view-mode)
	(erase-buffer)
	(insert txt)
        (cedille-mode-highlight-shadowed)
	(setq buffer-read-only t)
	(goto-char 1))
      (cedille-mode-rebalance-windows)
      (setq deactivate-mark nil)
      buffer)))

(defun cedille-mode-inspect-clear-all ()
  (interactive)
  (let* ((pins (se-get-pins 'se-interactive))
	 (len (length pins)))
    (se-pin-clear-all 'se-interactive)
    (se-mapc 'se-inf-clear-span-interactive (se-mode-parse-tree))
    (cedille-mode-inspect)
    (message "Cleared %s interactive call%s" len (cedille-mode-inspect-plural len))))

(defun cedille-mode-inspect-clear ()
  (interactive)
  (when se-mode-selected
    (let* ((span (se-first-span (se-mode-selected)))
	   (s (se-span-start span))
	   (e (se-span-end span))
	   (pins (se-pins-at s e 'se-interactive))
	   (len (length pins)))
      (se-unpin-list pins)
      (se-inf-clear-span-interactive span)
      (message "Cleared %s interactive call%s from node" len (cedille-mode-inspect-plural len)))
    (cedille-mode-inspect)))

(defun cedille-mode-inspect-plural (num)
  "Returns 's' if num != 1, else ''"
  (if (equal 1 num) "" "s"))

(provide 'cedille-mode-inspect)
