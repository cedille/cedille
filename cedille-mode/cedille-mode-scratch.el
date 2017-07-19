;;; Scratch buffer ;;;


(make-variable-buffer-local
 (defvar cedille-mode-scratch-prev ""
   "The previously inserted text. Used when the user types '='"))

(define-minor-mode cedille-scratch-mode
  "Creates scratch mode, which overrides M-c so that you can't copy the scratch buffer into the scratch buffer, and provides M-d, which deletes the contents of the scratch buffer."
  nil nil
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "M-d") #'cedille-mode-scratch-erase-all)
    (define-key map (kbd "M-+") (make-cedille-mode-resize-current-window 1))  ; increase and lock size of window
    (define-key map (kbd "M--") (make-cedille-mode-resize-current-window -1)) ; decrease and lock size of window
    (define-key map (kbd "M-=") #'cedille-mode-scratch-equal)    ; unlock size of window then resizes it
    (define-key map (kbd "M-<return>") #'cedille-mode-scratch-newline)
    map))

(defun cedille-mode-scratch-newline ()
  (interactive)
  (cedille-mode-scratch-display-text ""))

(defun cedille-mode-scratch-equal ()
  (interactive)
  (cedille-mode-scratch-display-text cedille-mode-scratch-prev t))

(defun cedille-mode-scratch-repeat (str times &optional acc)
  "Repeats str times times"
  (unless acc (setq acc ""))
  (if (equal 0 times)
      acc
      (cedille-mode-scratch-repeat str (- times 1) (concat acc str))))

(defun cedille-mode-scratch-display-text (text &optional dont-insert)
  "Displays text in given buffer. You probably shouldn't use dont-insert."
  (with-current-buffer (cedille-mode-scratch-buffer)
    (setq cedille-mode-scratch-prev text)
    ;(goto-char 1)
    ;(cedille-scratch-mode)
    (setq buffer-text (buffer-string))
    (erase-buffer)
    (insert text)
    (display-buffer (cedille-mode-scratch-buffer-name))
    (with-selected-window (get-buffer-window)
      (setq window-size-fixed nil)
      (fit-window-to-buffer)
      (setq sep-line (cedille-mode-scratch-repeat "-" (window-body-width))))
    (erase-buffer)
    (if dont-insert
	(insert buffer-text)
        (if (string= buffer-text "")
	    (insert text)
	    (insert (concat text "\n" sep-line "\n" buffer-text))))
    (goto-char 1)))

(defun cedille-mode-scratch-copy ()
  "Copies the contents of a buffer into the scratch buffer"
  (interactive)
  (setq text (buffer-string))
  (when (string-suffix-p "\n" text) (setq text (substring text 0 (- (length text) 1))))
  (setq text (concat "Buffer: " (buffer-name) "\n" text))
  (cedille-mode-close-active-window)
  (cedille-mode-scratch-display-text text))

(defun cedille-mode-scratch-erase-all ()
  "Erases all text in the scratch buffer. The reason I use this instead of simply erase-buffer is so that the user isn't prompted whether or not they really want to use the disabled command erase-buffer."
  (interactive)
  (with-current-buffer (cedille-mode-scratch-buffer)
    (erase-buffer)))

(defun cedille-mode-scratch-buffer-name ()
  "*cedille-scratch")

(defun cedille-mode-scratch-buffer ()
  "Creates or gets the scratch buffer"
  (setq buffer (get-buffer-create (cedille-mode-scratch-buffer-name)))
  (with-current-buffer buffer (set-input-method "Cedille")
		       (cedille-scratch-mode))
  buffer)

(provide 'cedille-mode-scratch)
