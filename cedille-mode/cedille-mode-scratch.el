;;;;;;;        Scratch buffer code        ;;;;;;;;

(require 'se-inf)

(defun cedille-mode-scratch-repeat (str times &optional acc)
  "Repeats str times times"
  (unless acc (setq acc ""))
  (if (equal 0 times)
      acc
      (cedille-mode-scratch-repeat str (- times 1) (concat acc str))))

(defun cedille-mode-scratch-insert-text (text)
  "Inserts TEXT in the scratch buffer."
  (with-current-buffer (cedille-mode-scratch-buffer)
    (display-buffer (cedille-mode-scratch-buffer-name))
    (with-selected-window (get-buffer-window)
      (setq buffer-text (or (buffer-string) ""))
      (erase-buffer)
    (if (string= buffer-text "")
	(insert text)
      (insert (concat text "\n" (cedille-mode-scratch-repeat "-" (window-body-width)) "\n" buffer-text)))
    (goto-char 1)))
  (cedille-mode-rebalance-windows))

(defun cedille-mode-scratch-copy-span ()
  "Copies the selected span to the scratch buffer"
  (interactive)
  (if (null se-mode-selected)
      (message "Error: must select a node")
      (setq span (se-first-span se-mode-selected)
	    s (se-span-start span)
	    e (min (buffer-size) (se-span-end span))
	    text (buffer-substring-no-properties s e))
      (cedille-mode-scratch-insert-text text)))

(defun cedille-mode-scratch-copy-buffer ()
  "Copies the contents of a buffer into the scratch buffer"
  (interactive)
  (setq text (buffer-string)
	len (length text))
  (when (string-suffix-p "\n" text)
    (setq text (substring text 0 (- len 1)))
    (decf len))
  (cedille-mode-close-active-window)
  (cedille-mode-scratch-insert-text text))

(defun cedille-mode-scratch-buffer-name ()
  "*cedille-scratch*")

(defun cedille-mode-scratch-buffer ()
  "Creates or gets the scratch buffer"
  (let ((parent cedille-mode-parent-buffer)
        (buffer (get-buffer-create (cedille-mode-scratch-buffer-name)))
        (window (cedille-mode-get-create-window (cedille-mode-scratch-buffer-name))))
        ;(buffer (get-buffer-create (cedille-mode-scratch-buffer-name))))
    (with-current-buffer buffer
      (set-input-method "Cedille")
      (setq cedille-mode-parent-buffer parent
            buffer-read-only nil))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-scratch-toggle (&optional jump-to-window-p)
  (interactive)
  (let* ((buffer (get-buffer-create (cedille-mode-scratch-buffer-name)))
	 (window (get-buffer-window buffer)))
    (if window
	(progn
	  (delete-window window)
	  (cedille-mode-rebalance-windows)
	  nil)
      (let ((window (cedille-mode-get-create-window buffer)))
	(when jump-to-window-p (select-window window)))
      (cedille-mode-scratch-buffer))))

(provide 'cedille-mode-scratch)
