(require 'tq)
(require 'json)

(eval-when-compile (require 'cl))

(defvar se-inf-parsing-header nil "If non-nil, displays header during parsing")

(make-variable-buffer-local
 (defvar se-inf-process nil
   "Holds process for current buffer in se-mode.  Processes are
started with `start-process'."))

(make-variable-buffer-local
  (defvar se-inf-json nil "The direct rest of reading the JSON from the backend (for debugging)."))

(make-variable-buffer-local
 (defvar se-inf-queue nil
   "Transaction queue for `se-inf-process'."))

(make-variable-buffer-local
 (defvar se-inf-modify-response (lambda (response) response)
   "A function that takes a response from the back end as an argument and returns a modified response."))

(make-variable-buffer-local
 (defvar se-inf-progress-fn nil
   "A function that recieves progress updates from the process"))

(make-variable-buffer-local
 (defvar se-inf-progress-prefix nil
    "String prefix that determines if a response is a progress update"))

; might need to UNDO:
(make-variable-buffer-local
 (defvar se-inf-response-hook nil
  "Functions to be evaluated after response of `se-inf-ask',
response given as only argument.  If `se-inf-response-is-json' is
non-nil the response is parsed as JSON first."))

(make-variable-buffer-local
 (defvar se-inf-init-spans-hook nil
   "Hooks to run when the spans have been set, but before
creating the parse tree from them."))

(make-variable-buffer-local
 (defvar se-inf-get-message-from-filename (lambda (x) x)
   "A function to call to compute the message to send to the backend 
a buffer is supposed to be parsed.  The function will be given the
name of the file to parse, and should return the message that ought
to be sent to the backend to request parsing of that file."))

(make-variable-buffer-local
 (defvar se-inf-response-finished nil
   "Set to true after a processing/parsing response has been received and
`se-inf-post-parse-hook' is executed."))

(make-variable-buffer-local
 (defvar se-inf-interactive-running nil
   "Non-nil when an interactive call is running"))

(make-variable-buffer-local
 (defvar se-inf-pre-parse-hook (list #'se-inf-save #'se-inf-remove-overlays)
   "Functions to be evaluated before parse request."))

(make-variable-buffer-local
 (defvar se-inf-post-parse-hook nil
   "Functions to be evaluated after parse request."))

(make-variable-buffer-local
 (defvar se-inf-interactive-response-hook nil
   "Functions to be evaluated after an interactive response has finished"))

(make-variable-buffer-local
 (defvar se-inf-response-is-json t
   "Non-nil if `se-inf-process' should return JSON.  See
`se-inf-post-parse-hook'."))

(make-variable-buffer-local
 (defvar se-inf-header-queue nil
   "The queue of header strings to show for consecutive interactive calls"))

(make-variable-buffer-local
 (defvar se-inf-headers ""
   "The headers to show in the header line (should be a 4-length vector or an empty string)"))

(make-variable-buffer-local
 (defvar se-inf-header-index 0
   "Current index of the header loop."))

(defvar se-inf-header-line-format nil
  "Format to set `header-line-format' to during background
parsing.")

(make-variable-buffer-local
 (defvar se-inf-header-timer nil
   "Stores active timer during background parsing."))

(defvar se-inf-header-timer-interval 0.25
  "Time in seconds between updating the header mode line.")

(defun se-inf-start (proc &optional no-auto-kill)
  "Initialize necessary variables to use se-inf functions.
Expects PROC to be the process returned from `start-process'.
Should be called at the start of an `se-mode'.

When NO-AUTO-KILL is nil the user will not be queried about PROC
still being active upon exiting emacs."
  (se-inf-put-remove-interactive-property 1 (+ 1 (buffer-size)))
  (unless (process-get proc 'se-inf-queue)
    (process-put proc 'se-inf-queue (tq-create proc))
    (process-put proc 'se-inf-auto-kill (not no-auto-kill)))
  (setq se-inf-process proc
	se-inf-queue (process-get proc 'se-inf-queue)))

(defun se-inf-stop ()
  "Should be called at the end of an `se-mode' session.  This
will kill the process, should be skipped if process is shared."
  (tq-close se-inf-queue)
  (kill-buffer (tq-buffer se-inf-queue))
  (when (car se-inf-queue)
    (setq se-inf-header-queue nil
	  se-inf-headers ""
	  header-line-format nil)
    (let* ((current (nth 1 (cdr (car (car se-inf-queue)))))
	   (symbol (nth 0 current))
	   (span (nth 4 current))
	   (pins (when span (se-pins-at (se-span-start span) (se-span-end span) 'se-interactive))))
      (se-unpin-list (se-inf-filter-pins-symbol symbol pins '())))))

(defun se-inf-interactive-h (q-str-or-fn response-fn extra span progress-fn header restore)
  (let* ((span (se-get-span span))
	 (header (or header ""))
	 (q-str (cond
		 ((stringp q-str-or-fn) q-str-or-fn)
		 (span (funcall q-str-or-fn extra span))
		 (t (funcall q-str-or-fn extra))))
	 (q (concat (se-inf-escape-string q-str) "\n"))
	 (data (list q-str-or-fn response-fn progress-fn span extra restore (buffer-name))))
    (setq se-inf-interactive-running t)
    (se-inf-queue-header header)
    (tq-enqueue se-inf-queue q "\n" data #'se-inf-interactive-response)))
  ;(setq se-inf-int-time (current-time)))

(cl-defun se-inf-interactive (q-str response-fn extra &key progress-fn header)
  "Sends an interactive request to the backend.
Keywords supported: progress-fn and header
Q-STR should be a query string to send to the backend.
RESPONSE-FN should be nil or a function that takes the backend's response and EXTRA.
EXTRA can be anything.
PROGRESS-FN, if non-nil, should be a function that takes the same arguments as RESPONSE-FN and returns a string to send to the backend (should probably be used as a stub).
HEADER, if non-nil, should be a string to display in the header line."
  (se-inf-interactive-h q-str response-fn extra nil progress-fn header nil))

(cl-defun se-inf-interactive-with-span (q-str-or-fn response-fn extra span &key progress-fn header restore)
  "Sends an interactive request to the backend.
Keywords supported: progress-fn, header, and restore.
Q-STR-OR-FN should either be a string or a function that takes the arguments EXTRA and SPAN and returns a query string for the backend.
RESPONSE-FN should be either nil or a function that takes the backend's response, EXTRA, and SPAN. If you want to add an 'interactive' attribute to the span, return a dotted pair (symbol . some-str).
EXTRA can be anything.
SPAN should be a span.
PROGRESS-FN, if non-nil, should be a function that takes the same arguments as RESPONSE-FN and returns a string to send to the backend (should probably be used as a stub).
HEADER, if non-nil, should be a string to display in the header line.
RESTORE, if non-nil, will make this call get recomputed during batch processing. If it is t, then RESPONSE-FN will get used; otherwise, it is assumed to be a function and will get called instead."
  (se-inf-interactive-h q-str-or-fn response-fn extra span progress-fn header restore))

(defun se-inf-ask (q-str)
  "Sends an input string to the backend and prints the response"
  (interactive "MQuery:")
  (se-inf-interactive q-str (lambda (response extra) (message response)) nil :header "Waiting"))

(defun se-inf-interactive-response (data response)
  "Receives a response from an `se-inf-interactive' call"
  ;(se-print-time se-inf-int-time)
  ;(message "response: %s" response)
  (let ((q-str-or-fn (nth 0 data))
	(response-fn (nth 1 data))
        (progress-fn (nth 2 data))
	(span (nth 3 data))
	(extra (nth 4 data))
	(restore (nth 5 data))
	(buffer (nth 6 data)))
    (with-current-buffer buffer
      (let* ((response (funcall se-inf-modify-response (se-inf-undo-escape-string response)))
             (pair (lambda (response-fn response)
                     (cond
                      ((null response-fn) nil)
                      (span (funcall response-fn response extra span))
                      (t (funcall response-fn response extra))))))
        (if (and progress-fn (string= se-inf-progress-prefix (substring response 0 (length se-inf-progress-prefix))))
            (let ((msg (funcall pair progress-fn (substring response (length se-inf-progress-prefix)))))
              (tq-enqueue se-inf-queue (concat msg "\n") "\n" data #'se-inf-interactive-response t))
          (se-inf-next-header)
          (let ((pr (funcall pair response-fn response)))
            (when (and span pr (car-safe pr) (cdr-safe pr)) (se-inf-add-to-span span pr)))
          (when restore
            (let ((restore-data (list q-str-or-fn (if (eq t restore) response-fn restore) progress-fn extra))
                  (s (if span (se-span-start span) 1))
                  (e (if span (se-span-end span) 1)))
              (se-inf-remove-dup-pin (se-pins-at s e 'se-interactive) restore-data)
              (se-pin-data s e 'se-interactive restore-data)))
          (run-hooks 'se-inf-interactive-response-hook))))))

(defun se-inf-add-to-span (span pair)
  "Adds pair to list of span's interactive properties"
  (let* ((data (se-span-data span))
	 (int (cdr (assoc 'se-interactive data)))
	 (int (assq-delete-all (car pair) int))
	 (int (append int (list pair)))
	 (data (assq-delete-all 'se-interactive data)))
    (setf (se-span-data span) (append data (list (cons 'se-interactive int))))))

(defun se-inf-remove-dup-pin (pins data)
  "Removes duplicate 'se-interactive pin so that repeated calls to the same span won't be needlessly done again during re-processing"
  (when pins
    (let ((h (car pins)))
      (if (equal data (se-pin-item-data h))
	  (se-unpin h) ; No need to go further
        (se-inf-remove-dup-pin (cdr pins) data)))))

(defun se-inf-run-pins(pins queued total)
  "Recursively iterates through pins and calls each function with its args (span and question)"
  (when pins
    (let* ((h (car pins))
	   (data (se-pin-item-data h))
	   (start (se-pin-item-start h))
	   (end (se-pin-item-end h))
	   (span (se-span-from start end))
	   (q-str-or-fn (nth 0 data))
	   (response-fn (nth 1 data))
           (progress-fn (nth 2 data))
	   (extra (nth 3 data))
	   (header (format "Recomputing interactive calls (%s/%s)" queued total)))
      (if span
	  (se-inf-interactive-h q-str-or-fn response-fn extra span progress-fn header nil)
	(se-unpin h))
      (se-inf-run-pins (cdr pins) (+ 1 queued) total))))

(defun se-inf-restore-interactive ()
  "Restores interactive calls"
  (let ((pins (se-get-pins 'se-interactive)))
    (when pins (se-inf-run-pins pins 0 (length pins)))))

(defun se-inf-finish-response ()
  "Stops the header timer, sets `se-inf-response-finished' to t, resets the header, etc..."
  (se-inf-header-timer-stop)
  (setq se-inf-headers "")
  (setq se-inf-interactive-running nil))

(defun se-inf-clear-span-interactive (span)
  "Clears the interactive properties from span"
  (assq-delete-all 'se-interactive (se-span-data span)))

(defun se-inf-process-response (response buffer)
  "Called to evaluate `se-inf-post-parse-hook' upon response from
`se-inf-process'."
  (condition-case err
      (with-current-buffer buffer
	(unwind-protect
	    (if se-inf-response-is-json
                (let* ((json-array-type 'list)
		       (json (json-read-from-string response)))
                  (setq se-inf-json json)
		  (run-hook-with-args 'se-inf-post-parse-hook json))
	      (run-hook-with-args 'se-inf-post-parse-hook response))
	  (se-inf-restore-interactive)
	  (setq se-inf-response-finished t)))
    (error
     (message "%s" (error-message-string err))))
  nil)

(defun se-inf-parse-file (&optional file)
  "Sends parse request to current process.  Uses the current
buffer's file unless FILE is non-nil."
  (interactive)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (let ((ms (se-inf-get-message-from-filename (or file (buffer-file-name)))))
    (se-inf-interactive ms #'se-inf-process-response (buffer-name) :progress-fn se-inf-progress-fn :header se-inf-parsing-header)))

(defun se-inf-add-final-newline ()
  "Silently adds a newline to the end of the buffer, if necessary"
  (let ((size (buffer-size))
	(pos (point))
	(mark-pos (mark))
	(mark-act mark-active))
    (when (or (equal 0 size) (not (string= "\n" (buffer-substring size (1+ size)))))
      (with-silent-modifications
	(goto-char (point-max))
	(insert "\n")
	(goto-char pos)
	(push-mark mark-pos t mark-act)
	(setq mark-active mark-act)))))

(defun se-inf-save ()
  "Saves the current buffer"
  (interactive)
  (se-inf-add-final-newline)
  (save-buffer))

(defun se-inf-get-message-from-filename (filename)
  "Calls the function variable `se-inf-get-message-from-filename'"
  (funcall se-inf-get-message-from-filename filename))

(defun se-inf-get-spans (json)
  "Returns spans from default formatted JSON."
  (cdr (assoc 'spans json)))

(defun se-inf-process-spans (json)
  "Creates parse tree from spans found in JSON. Sets the variables
`se-mode-parse-tree' and `se-mode-spans'."
  (when (se-inf-get-spans json)
    (setq se-mode-spans
          (sort (se-create-spans (se-inf-get-spans json)) 'se-term-before-p))
    (run-hooks 'se-inf-init-spans-hook)
    (setq se-mode-parse-tree
	  (se-create-parse-tree se-mode-spans))))

(defun se-inf-get-error (json)
  "Returns possible error from default formatted JSON."
  (cdr (assoc 'error json)))

(defun se-inf-process-error (json)
  "Displays error message found in JSON."
  (let ((msg (se-inf-get-error json)))
    (when msg (message "Error: %s" msg) t)))

(defun se-inf-get-error-span (json)
  "Returns possible error spans from default formatted JSON."
  (let ((data (cdr (assoc 'error-span json))))
    (cond
     ((or (null data) (< (length data) 3))
      nil)
     ((consp (car data))
      (mapcar (lambda (span) (apply #'se-new-span span)) data))
     (t
      (apply #'se-new-span data)))))

(defun se-inf-process-error-span (json)
  "Highlights the error spans found in JSON."
  (let ((data (se-inf-get-error-span json)))
    (cond
     ((null data) nil)
     ((se-span-p data)
      (se-inf-error-overlay data)
      (se-mode-goto-term data))
     (t
      (mapc #'se-inf-error-overlay data)
      (se-mode-goto-term (car data))))))

(defun se-inf-remove-overlays (&rest args)
  "Removes all overlays from the current buffer."
  (with-silent-modifications
    (remove-overlays (point-min) (point-max))))

(defun se-inf-error-overlay (span)
  "Creates an overlay over SPAN to indicate an error."
  (with-silent-modifications
    (let ((overlay (make-overlay (se-term-start span)
				 (se-term-end span))))
      (overlay-put overlay 'info (se-span-data (se-first-span span)))
      (overlay-put overlay 'face "error")
      (overlay-put overlay 'modification-hooks
		   (list (lambda (overlay &rest args)
			   (overlay-put overlay 'face nil)))))))

(defun se-inf-kill-emacs-advice (orig &optional arg)
  "Don't query about killing processes if they have
`se-inf-auto-kill' set to a non-nil value."
  (let ((non-auto-kill-procs
	 (cl-remove-if (lambda (proc) (process-get proc 'se-inf-auto-kill)) (process-list))))
    (cl-letf (((symbol-function 'process-list) (lambda () non-auto-kill-procs)))
      (funcall orig arg))))

(if (fboundp #'advice-add)
    (advice-add #'save-buffers-kill-emacs :around #'se-inf-kill-emacs-advice))

(defun se-inf-parse-and-wait ()
  "Send a parse request to the current process and wait for a
response.  Raises an error if `se-mode-parse-tree' is nil after
the response is processed or on user inturruption."
  (setq se-mode-parse-tree nil)
  (se-inf-parse-file)
  (while (and (null se-inf-response-finished)
	      (not (input-pending-p)))
    (sleep-for 0.01))
  (cond
   ((input-pending-p)
    (error "Interrupted by user input."))
   ((null se-mode-parse-tree)
    (error "Null parse tree.")))
  (se-mode-clear-selected)
  (se-mode-set-spans))

(defun se-inf-put-remove-interactive-property (start end)
  "Puts the text property 'insert-in-front-hooks to the range from start to end, with the value being `se-inf-remove-interactive-props'"
  ; This clears all former 'insert-in-front-hooks properties,
  ; but this will have no consequence since the text is inserted
  ; and this property shouldn't matter on fresh text
  (with-silent-modifications
    (put-text-property start end 'insert-in-front-hooks (list #'se-inf-remove-interactive-props))))

(defun se-inf-filter-pins-symbol (symbol pins so-far)
  "Filters out pins without symbol"
  (if (null pins)
      so-far
      (let* ((h (car pins))
	     (symbol2 (car (se-pin-item-data h))))
	(when (equal symbol symbol2)
	  (setq so-far (cons h so-far)))
	(se-inf-filter-pins-symbol symbol (cdr pins) so-far))))

(defun se-inf-remove-interactive-props (start end)
  "Removes se-interactive properties from inserted text if it was pasted"
  (with-silent-modifications (put-text-property start end 'se-pin nil)))

(defun se-inf-escape-string (text)
  "Replaces all \\n and \\\" characters with \\\\n and \\\\\""
  "The above documentation is for when using C-h f. If you are reading this inside the code, then the documentation is:"
  "Replaces all \n and \" characters with \\n and \\\""
  (replace-regexp-in-string "\"" "\\\\\"" (replace-regexp-in-string "\n" "\\\\n" text)))

(defun se-inf-undo-escape-string (text)
  "Undoes the effects of `se-inf-escape-string' (technically a backend function should do this) upon receiving a response from the backend"
  ; Removes the '\n' at the end and replaces all '\\n' and '\\\"' with '\n' and '\"'
  (replace-regexp-in-string "\\\\\"" "\"" (replace-regexp-in-string "\\\\n" "\n" (replace-regexp-in-string "\n\\'" "" text))))

(defun se-inf-header-timer-start ()
  "Starts timer to increment `se-inf-header-index' and update
header mode line during background parsing.  Used to simulate a
hourglass feature."
  (when se-inf-header-timer
    (cancel-timer se-inf-header-timer))
  (setq header-line-format se-inf-header-line-format)
  (lexical-let ((buffer (buffer-name)))
    (setq se-inf-header-timer
	  (run-with-timer 0 se-inf-header-timer-interval
			  (lambda ()
			    (with-current-buffer buffer
			      (incf se-inf-header-index)
			      (force-mode-line-update)))))))

(defun se-inf-header-timer-stop ()
  "Stops the header timer in `se-inf-header-timer'.  See
`se-inf-header-timer-start' for more information."
  (when se-inf-header-timer
    (cancel-timer se-inf-header-timer))
  (setq header-line-format nil)
  (force-mode-line-update))

(defun se-inf-set-header-format ()
  (setq se-inf-header-line-format
	(unless (or (null se-inf-headers) (equal "" se-inf-headers))
	  '(:eval (aref se-inf-headers (mod se-inf-header-index 4))))))

(defun se-inf-string-to-header (str)
  (list (vector (concat str "|") (concat str "/") (concat str "―") (concat str "\\"))))

(defun se-inf-queue-header (str)
  "Adds str to  `se-inf-header-queue'"
  (if (string= str "")
      (setq se-inf-header-queue (append se-inf-header-queue (list "")))
    (let ((str (concat " " str " ")))
      (setq se-inf-header-queue (append se-inf-header-queue (se-inf-string-to-header str)))
      (when (and (null header-line-format) (equal 1 (length se-inf-header-queue)))
	(se-inf-next-header)))))

(defun se-inf-next-header ()
  "If `header-line-format' is nil, then sets it to be the first element from `se-inf-header-queue', which gets popped"
  (when (or se-inf-header-queue se-inf-interactive-running)
    (let* ((popped (pop se-inf-header-queue)))
      (if (and (null popped) (null se-inf-header-queue))
	  (se-inf-finish-response)
	(setq se-inf-headers popped)
	(se-inf-set-header-format)
	(se-inf-header-timer-start)))))

(provide 'se-inf)
