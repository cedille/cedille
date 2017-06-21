(load-library "cedille-mode-parent")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;          Normalize Code          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;       Variables and Helpers       ;;;;;;;;

(defvar cedille-mode-normalize-headers
  (vector " Normalizing |" " Normalizing /" " Normalizing -" " Normalizing \\")
  "A loop of strings to show while normalizing is happening in the background.  Supposed to be similar to an hourglass.")

(make-variable-buffer-local
 (defvar cedille-mode-normalize-header-index 0
   "Current index of the header loop."))

(defvar cedille-mode-normalize-header-line-format
  '(:eval (aref cedille-mode-normalize-headers (mod cedille-mode-normalize-header-index 4)))
  "Format to set `header-line-format' to during background normalizing.")

(make-variable-buffer-local
 (defvar cedille-mode-normalize-header-timer nil
   "Stores active timer during background parsing."))

(defvar cedille-mode-normalize-header-timer-interval 0.25
  "Time in seconds between updating the header mode line.")

(defvar sep "§")
(defvar sep2 "⦀") ; Needed some character that will probably never get used to seperate context definition elements


(defun rev-h(list reversed)
  "rev helper"
  (if (endp list) reversed (rev-h (rest list) (list* (first list) reversed))))

(defun rev(list)
  "Reverses a list"
  (rev-h list '()))





(defun cedille-mode-normalize()
  "Does something"
  (interactive)
  (if se-mode-selected
    (let ((lang-level (cdr (assoc 'language-level (se-term-data (se-mode-selected))))))
      (if (and lang-level (or (string= lang-level "term") (string= lang-level "type")))
	  (progn
	    (cedille-mode-normalize-header-timer-start)
	    (se-inf-ask (normalize-request-text lang-level) 'cedille-mode-normalize-receive-response))
	(message "Selected span must be a term or a type")))
    (call-interactively 'cedille-mode-normalize-prompt)))





;;;;;;;;       Span Code       ;;;;;;;;


(defun normalize-request-text(lang-level)
  "Gets the text to send to the backend as a request to normalize a span"
  (setq sp (se-term-start (se-mode-selected)))
  (setq ep (se-term-end (se-mode-selected)))
  (concat "normalize"
	  sep lang-level
	  sep (buffer-substring-no-properties sp ep)
	  sep (format "%s" sp)
	  sep (format "%s" ep)
	  sep (file-truename (buffer-file-name))
	  sep (cedille-mode-local-context-param)))

(defun cedille-mode-local-context-param()
  "Formats the local context into a string suitable to be sent to the backend"
  (let ((original-context cedille-mode-original-context-list) (out ""))
    (when original-context
      (let* ((ctxt (copy-tree original-context))
	     (terms (cedille-mode-shadow-filter (car ctxt)))
	     (types (cedille-mode-shadow-filter (cdr ctxt))))
        (while terms
          (setq item (pop terms))
          (setq out (concat out sep "term" sep2 (car item) sep2 (cdr (assoc 'value item)))))
	(while types
	  (setq item (pop types))
	  (setq out (concat out sep "type" sep2 (car item) sep2 (cdr (assoc 'value item)))))))
    out))

(defun cedille-mode-shadow-filter(lst)
  (let (shadowed-lst)
    (dolist (pair (reverse lst) shadowed-lst)
      (let* ((symbol (car pair)) (matches (lambda (thispair) (equal (car thispair) symbol))))
	(setq shadowed-lst (cons pair (remove-if matches shadowed-lst)))))
    shadowed-lst))

(defun cedille-mode-selected-as-string()
  "Gets the entire selected node as a string"
  (buffer-substring-no-properties
   (se-term-start (se-mode-selected))
   (se-term-end (se-mode-selected))))

(defun cedille-mode-normalize-receive-response(buffer text)
  "Receives the normalize text response from the backend. Handler for when the user requested a span to be normalized."
  (setq text (replace-regexp-in-string "\n\\'" "" text))
  (setq split (split-string text sep))
  (setq text (nth 0 split))
  (setq start (string-to-number (nth 1 split)))
  (setq end (string-to-number (nth 2 split)))
  (with-current-buffer buffer
    (cedille-mode-normalize-header-timer-stop)
    (let* ((sel (span-from start end se-mode-parse-tree))
	   (name (se-term-name sel))
	   (data (se-term-data sel))
	   (revd (rev data)))
      (add-to-list 'revd (cons 'normalized text))
      (setq data (rev revd))
      (setq new (se-new-span name start end data))
      (cedille-mode-normalize-replace-in-tree-parent new sel (se-mode-parse-tree)))
    (open-inspect-buffer-if-closed)
    (cedille-mode-rebalance-windows)
    (pin-data-to-region start end 'norm (cons start end))
    (message (format "pinned: %s" (get-all-pinned 'norm)))
    )
  (message "done receiving response"))

(defun open-inspect-buffer-if-closed()
  "Updates the inspect buffer and opens it if it is closed"
  (display-buffer (cedille-mode-inspect-buffer))
  (cedille-mode-inspect))

(defun span-from(start end tree)
  "Finds a span that ranges from start to end in tree"
  (typecase tree
    (se-node
     (setq parent (se-node-parent tree))
     (if (and (eq start (se-span-start parent)) (eq end (se-span-end parent)))
	 parent
         (se-map-1 (se-curry #'span-from start end) (se-node-children tree))))
    (sequence
     (se-map-1 (se-curry #'span-from start end) tree))))

(defun cedille-mode-normalize-replace-in-tree-parent(new old tree)
  "Finds old in tree and sets it parent to new"
  (typecase tree
    (se-node
     (if (equal old (se-node-parent tree))
	   (setf (se-node-parent tree) new)
           (se-map-1 (se-curry #'cedille-mode-normalize-replace-in-tree-parent new old) (se-node-children tree))))
    (sequence
     (se-map-1 (se-curry #'cedille-mode-normalize-replace-in-tree-parent new old) tree))))

(defun cedille-mode-normalize-header-timer-start ()
  "Starts timer to increment `cedille-mode-normalize-header-index' and update header mode line during background normalizing. Used to simulate an hourglass feature."
  (when cedille-mode-normalize-header-timer
    (cancel-timer cedille-mode-normalize-header-timer))
  (setq header-line-format cedille-mode-normalize-header-line-format)
  (lexical-let ((buffer (buffer-name)))
    (setq cedille-mode-normalize-header-timer
	  (run-with-timer 0 cedille-mode-normalize-header-timer-interval
			  (lambda ()
			    (with-current-buffer buffer
			      (incf cedille-mode-normalize-header-index)
			      (force-mode-line-update)))))))

(defun cedille-mode-normalize-header-timer-stop ()
  "Stops the header timer in `cedille-mode-normalize-header-timer'. See `cedille-mode-normalize-header-timer-start' for more information."
  (when cedille-mode-normalize-header-timer
    (cancel-timer cedille-mode-normalize-header-timer))
  (setq header-line-format nil)
  (force-mode-line-update))






;;;;;;;;       Prompt Code       ;;;;;;;;


(defun cedille-mode-display-normalize-text(buffer text)
  "Displays text in given buffer"
  ;(interactive)
  (with-current-buffer (cedille-mode-normalize-buffer)
    (setq buffer-read-only nil)
    (setq buffer-text (buffer-string))
    (erase-buffer)
    (if (string= buffer-text "")
	(insert text)
      (insert text "\n\n" buffer-text))
    (setq buffer-read-only t)
    (display-buffer (cedille-mode-normalize-buffer-name)))
  (rebalance-normalize-window (get-buffer-window (cedille-mode-normalize-buffer)) text))

(defun cedille-mode-normalize-buffer-name() "*cedille-normalize*")

(defun cedille-mode-normalize-buffer()
  "Creates or gets the normalize buffer"
  (get-buffer-create (cedille-mode-normalize-buffer-name)))

(defun rebalance-normalize-window(win text)
  "Rebalances the normalize window size"
  (with-selected-window win
    (setq width (window-body-width))
    (setq height (window-body-height))
    (setq lines (num-lines width text))
    (setq delta (- lines height))
    (enlarge-window delta)))

(defun num-lines(w text)
  "Returns the number of lines it will take to insert text into a buffer with width number of characters horizontally"
  (num-lines-h w text 1 0))

(defun num-lines-h(w text lines chars)
  "Helper for `num-lines'"
  (if (string= text "") lines (num-lines-h-h w text lines chars)))

(defun num-lines-h-h(w text lines chars)
  "Helper for `num-lines-h'"
  (setq head (substring text 0 1))
  (setq tail (substring text 1 nil))
  (if (string= head "\n")
    (num-lines-h w tail (+ 1 lines) 0)
    (if (eq chars w)
      (num-lines-h w tail (+ 1 lines) 1)
      (num-lines-h w tail lines (+ 1 chars)))))

(defun cedille-mode-normalize-prompt(text)
  "Prompts the user to input an expression to normalize"
  (interactive "MNormalize: ")
  (cedille-mode-normalize-header-timer-start)
  (se-inf-ask (concat "normalize" sep text) 'cedille-mode-normalize-receive-response-prompt))

(defun cedille-mode-normalize-receive-response-prompt(buffer text)
  "Receives the normalize text response (or error text) from the backend. Handler for when the user typed an expression into the prompt."
  (setq text (replace-regexp-in-string "\n\\'" "" text)) ; Remove newline from end
  (setq text (replace-regexp-in-string "\\\\n" "\n" text)) ; Undo effects of escape-string from backend
  (setq text (replace-regexp-in-string "\\\\\"" "\"" text)) ; ^^^
  (with-current-buffer buffer (cedille-mode-normalize-header-timer-stop))
  (cedille-mode-display-normalize-text (cedille-mode-normalize-buffer) text))



(provide 'cedille-mode-normalize)
