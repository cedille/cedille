;;;;;;;;        Scratch buffer code        ;;;;;;;;


(make-variable-buffer-local
 (defvar cedille-mode-scratch-lines 0
   "The number of lines to set the window's height to when the user types '='"))

(define-minor-mode cedille-scratch-mode
  "Creates scratch mode, which overrides M-c so that you can't copy the scratch buffer into the scratch buffer, and provides M-d, which deletes the contents of the scratch buffer."
  nil nil
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap)
    (define-key map (kbd "d") #'cedille-mode-scratch-erase-all)
    (define-key map (kbd "=") #'cedille-mode-scratch-equal) ; Override cedille-mode-parent "=" keybinding
    (define-key map (kbd "x") #'cedille-mode-close-active-window)
    (define-key map (kbd "X") #'cedille-mode-close-active-window)
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "scratch mode"))
    map))


(defun cedille-mode-scratch-equal ()
  (interactive)
  (goto-char 1)
  (with-selected-window (cedille-mode-get-create-window (cedille-mode-scratch-buffer-name))
    (setq window-size-fixed nil
	  delta (- cedille-mode-scratch-lines (window-height)))
    (enlarge-window delta)))

(defun cedille-mode-scratch-repeat (str times &optional acc)
  "Repeats str times times"
  (unless acc (setq acc ""))
  (if (equal 0 times)
      acc
      (cedille-mode-scratch-repeat str (- times 1) (concat acc str))))

(defun cedille-mode-scratch-display-text (text)
  "Displays text in given buffer."
  (with-current-buffer (cedille-mode-scratch-buffer)
    (setq window-size-fixed nil
	  buffer-read-only nil
	  buffer-text (buffer-string))
    (erase-buffer)
    (setq text (cedille-mode-markup-propertize text))
    (insert text)
    (display-buffer (cedille-mode-scratch-buffer-name))
    (with-selected-window (get-buffer-window)
      (setq window-size-fixed nil)
      (fit-window-to-buffer)
      (setq cedille-mode-scratch-lines (window-height)
	    width (window-body-width)))
    (erase-buffer)
    (if (string= buffer-text "")
	(insert text)
        (insert (concat text "\n" (cedille-mode-scratch-repeat "-" width) "\n" buffer-text)))
    (goto-char 1)
    (setq buffer-read-only t
	  window-size-fixed t)))

(defun cedille-mode-scratch-copy-span ()
  "Copies the selected span to the scratch buffer"
  (interactive)
  (if (null se-mode-selected)
      (message "Error: must select a node")
      (setq span (se-first-span se-mode-selected)
	    s (se-span-start span)
	    e (min (buffer-size) (se-span-end span))
	    text (buffer-substring-no-properties s e))
      (cedille-mode-scratch-display-text text)))

(defun cedille-mode-scratch-copy-buffer ()
  "Copies the contents of a buffer into the scratch buffer"
  (interactive)
  (setq text (buffer-string)
	len (length text))
  (when (string-suffix-p "\n" text)
    (setq text (substring text 0 (- len 1)))
    (decf len))
  (cedille-mode-close-active-window)
  (cedille-mode-scratch-display-text text))

(defun cedille-mode-scratch-erase-all ()
  "Erases all text in the scratch buffer. The reason I use this instead of simply erase-buffer is so that the user isn't prompted whether or not they really want to use the disabled command erase-buffer."
  (interactive)
  (setq buffer-read-only nil)
  (erase-buffer)
  (setq buffer-read-only t))

(defun cedille-mode-scratch-buffer-name ()
  "*cedille-scratch*")

(defun cedille-mode-scratch-buffer ()
  "Creates or gets the scratch buffer"
  (let ((buffer (get-buffer-create (cedille-mode-scratch-buffer-name))))
    (with-current-buffer buffer
      (set-input-method "Cedille")
      (cedille-scratch-mode)
      (setq buffer-read-only t)
      (cedille-mode-scratch-equal))
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
