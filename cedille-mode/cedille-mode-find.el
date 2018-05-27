;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Debug info display
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-display-debug-text(text &optional extra)
  "Displays text in given buffer"
    (with-current-buffer (cedille-mode-debug-buffer)
        (setq buffer-read-only nil)
        (erase-buffer)
        (insert text)
        (setq buffer-read-only t)
        (display-buffer (cedille-mode-debug-buffer-name))
    )
)

(defun cedille-mode-debug-buffer-name()
    "*cedille-debug-info*"
)

(defun cedille-mode-debug-buffer()
  "Creates or gets the debug buffer"
    (get-buffer-create (cedille-mode-debug-buffer-name))
)

(defun cedille-mode-backend-debug()
  "Requests debug info from the cedille process and displays it in a new buffer"
    (interactive)
    (let ((debug-buffer (cedille-mode-debug-buffer)))
        (se-inf-interactive "debug" 'cedille-mode-display-debug-text nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Cedille Find
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-find-buffer-setup(display-string table)
  "Gets buffers and makes the call to setup the display buffer"
  (let ((summary-buffer 
	 (get-buffer-create (concat "*cedille-summary-" 
				    (file-name-nondirectory 
				     (file-name-sans-extension 
				      (buffer-file-name (other-buffer nil t)))) 
				    "*")))
	(main-buffer (other-buffer nil t)))
    (cedille-mode-summary-buffer-setup 
     table display-string summary-buffer main-buffer)
    (display-buffer summary-buffer)))

(defun cedille-mode-add-data-from-occurrence(table occurrence)
  "Add the data from the occurrence to table"
  (let ((defn (cdr (assoc 'defn occurrence)))
          (pos-info (cdr (assoc 'pos-info occurrence)))
          (filename (cdr (assoc 'filename occurrence))))
    (puthash (concat defn "," (number-to-string pos-info))
	     filename
	     table)))

(defun cedille-mode-construct-find-table(occurrences)
  "Return a hash table from defn,pos-info to filename from the occurrences array"
  (let ((table (make-hash-table :test #'equal)))
    (mapcar (lambda (occurrence) (cedille-mode-add-data-from-occurrence table occurrence)) occurrences) table))

(defun cedille-mode-find-process-data(json)
  "Converts JSON to hash table and display string, then calls buffer setup"
  (let* ((find-data (assoc 'find json))
	 (find-symb (cdr (assoc 'symbol find-data)))
	 (find-occurrences (cdr (assoc 'occurrences find-data)))
	 (find-table (cedille-mode-construct-find-table find-occurrences ))
	 (find-display-string (concat find-symb " occurrences:\n" 
				      (cedille-mode-keylist-to-string
				       (cedille-mode-get-hash-table-keys find-table)))))
    (cedille-mode-find-buffer-setup find-display-string find-table)))

(defun cedille-mode-find-process-response(text);buffer text)
  "Receives response from cedille process, converts it from text, and passes the data to be processed"
  (let ((json (json-read-from-string text)))
    (cedille-mode-find-process-data json)))

(defun cedille-mode-find-test()
  (se-inf-interactive "find§tt" 'cedille-mode-find-process-response))

(defun cedille-mode-find(start end)
  "Send the current symbol to the backend to get its occurrences"
  (interactive "r")
  (se-inf-interactive (concat "find§" (buffer-substring-no-properties start end)) 'cedille-mode-find-process-response))

(provide 'cedille-mode-find)
