;;;;INSPECT MODE
;;; This document contains code related to cedille inspect mode.
;;; This mode, called using the hotkey 'i', provides information about the selected span

;;TODO - make sure upon opening inspect mode that it goes to position 1

(defun cedille-mode-inspect-buffer-name() (concat "*cedille-inspect-" (file-name-base (buffer-name)) "*"))

(defun cedille-mode-inspect-buffer()
  (let* ((n (cedille-mode-inspect-buffer-name))
         (b (get-buffer-create n)))
    (with-current-buffer b
       (setq buffer-read-only nil))
    b))

(defun cedille-mode-inspect ()
  "Displays information on the currently selected node in 
the info buffer for the file.  Return the info buffer as a convenience."
  ;(interactive)
  (when se-mode-selected
    (let* ((buffer (cedille-mode-inspect-buffer))
           (d (se-term-to-json (se-mode-selected)))
           (txt (se-mode-pretty-json (if cedille-mode-debug d (cedille-mode-filter-out-special d)))))
      (with-current-buffer buffer
	(erase-buffer)
	(insert txt)
	(goto-char 1)
	(setq buffer-read-only t))
      (cedille-mode-rebalance-windows)
      (setq deactivate-mark nil)
      buffer)))

(provide 'cedille-mode-inspect)
