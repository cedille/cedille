(load-library "cedille-mode-parent")
(require 'cedille-mode-info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary retrieval
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-format-summary-text(text)
  "Remove newlines and instances of string ctor for display purposes"
    (replace-regexp-in-string "\n" " " 
                    (replace-regexp-in-string "^ctor" " " text))
)

(defun cedille-mode-get-summary-from-span(table span)
  "Pull the summary information from the span, and then insert it into the table"
    (let* ((data (se-span-data span))
            (summary (cdr (assoc 'summary data))))
        (if summary
            (puthash (cedille-mode-format-summary-text summary);(cedille-mode-markup-propertize-text summary))
                        (cons nil (se-span-start span)) ; nil signifies location within current file 
                        table) 
            () ; do nothing if summary does not exist
        )
    )
)

(defun cedille-mode-construct-summary-table()
  "Return a hash table with summary-text as key and (filename, start pos) as value"
  (let ((table (make-hash-table :test #'equal)))
        (mapcar 
            (lambda (span) 
                (cedille-mode-get-summary-from-span table span)
            )
            se-mode-spans
        )
        table
  )
)

(defun cedille-mode-get-hash-table-keys(table)
  "Return a list of keys(summary texts) from the summary table"
    (let ((keys ()))
        (maphash 
            (lambda(key val) (push key keys)) 
            table
        )
        (nreverse keys)
    )
)

(defun cedille-mode-keylist-to-string(keys)
  "Return a single string for display"
    (mapconcat 'identity keys "\n")
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary View minor-mode code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun cedille-mode-get-start-position(table)
  "Gets the start position of the text displayed on the current line"
    (let* ((key (substring (thing-at-point 'line t) 0 -1)) ; -1 to remove newline
            (location-pair (gethash key table))
            (start-pos (cdr location-pair)))
        start-pos
    )
)


(defun cedille-mode-summary-jump()
  "Jumps from the summary of a top-level definition to that definition"
    (interactive)
    (let ((start-pos (cedille-mode-get-start-position cedille-mode-summary-table)))
        (select-window (get-buffer-window cedille-mode-main-buffer))
        (goto-char start-pos)
        (se-navigation-mode)
        ; the following prevents highlighting errors when jumping to navigation mode buffer, copied from nav-jump
        (if mark-active 
            (progn  
                (exchange-point-and-mark 1) 
                (set-mark-command 1)))
        (message (concat "Jump to char:  " (number-to-string start-pos)))))

(define-minor-mode cedille-summary-view-mode
    "Creates summary mode, which allows jumping from a summary back to its top-level definition in the main window"
    nil         ; init-value, whether the mode is on automatically after definition
    " Summary"  ; indicator for mode line
    (let ((map (make-sparse-keymap)))
      (set-keymap-parent map cedille-mode-minor-mode-parent-keymap) ; inherit bindings from parent keymap
      (define-key map (kbd "m") 'cedille-mode-summary-jump)         ; jump to selected line
      (define-key map (kbd "s") #'cedille-mode-close-active-window) ; close summary mode
      (define-key map (kbd "S") #'cedille-mode-close-active-window) ; close summary mode
      (define-key map (kbd "h") (make-cedille-mode-info-display-page "summary mode"))
      map))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary View display code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-summary-buffer-name()
  "Generates a unique name for each file's summary"
    (concat "*cedille-summary-" (file-name-base) "*"))

(defun cedille-mode-summary-buffer()
  "Creates/gets and returns the summary buffer"
    (get-buffer-create (cedille-mode-summary-buffer-name)))

(defun cedille-mode-summary-buffer-setup(table display-string summary-buffer main-buffer)
    "Handle the buffer initialization for summary mode startup"
    (with-current-buffer summary-buffer
        (setq buffer-read-only nil)
        (erase-buffer)
        (insert display-string)
	;(cedille-buffer-display-text display-string)
        (setq buffer-read-only t)
        (setq cedille-mode-summary-table table)
        (make-local-variable 'cedille-mode-summary-table)
        (setq cedille-mode-main-buffer main-buffer)
        (make-local-variable 'cedille-mode-main-buffer)
	(message "updating summary buffer jumps...")
	;(cedille-buffer-update-jumps)
    )
    (cedille-mode-rebalance-windows)
)

(defun cedille-mode-summary()
    (let* ((summary-buffer (cedille-mode-summary-buffer))
           (summary-table (cedille-mode-construct-summary-table))
           (summary-string (cedille-mode-keylist-to-string 
                           (cedille-mode-get-hash-table-keys summary-table)))
           (main-buffer (current-buffer)))
        (cedille-mode-summary-buffer-setup summary-table summary-string summary-buffer main-buffer)
    )
)

(provide 'cedille-mode-summary)
