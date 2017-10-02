(require 'tq)
(require 'json)

(eval-when-compile (require 'cl))

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
 (defvar se-inf-modify-response nil
   "If non-nil, should be a function that takes a response from the back end as an argument and returns a modified response."))

; might need to UNDO:
(make-variable-buffer-local
 (defvar se-inf-respose-hook nil
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
 (defvar se-inf-filename #'buffer-file-name
   "The function to call when you want to get the filename of the current buffer"))

(make-variable-buffer-local
 (defvar se-inf-filename-base #'file-name-base
   "The function to call when you want to get the filename base of the current buffer"))

(make-variable-buffer-local
 (defvar se-inf-response-finished nil
   "Set to true after a processing/parsing response has been received and
`se-inf-post-parse-hook' is executed."))

(make-variable-buffer-local
 (defvar se-inf-interactive-running nil
   "Non-nil when an interactive call is running"))

(make-variable-buffer-local
 (defvar se-inf-pre-parse-hook (list #'save-buffer #'se-inf-remove-overlays)
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
	   (span (nth 3 current))
	   (pins (se-pins-at (se-span start span) (se-span-end span) 'se-interactive)))
      (se-unpin-list (se-inf-filter-pins-symbol symbol pins '())))))

(cl-defun se-inf-interactive (q-str-or-fn response-fn &key span header extra restore delay is-restore); batch-fn)
  "Sends an interactive request to the backend.
Keywords supported: span, batch-fn, header, extra, and restore.
Q-STR-OR-FN should be either a string or a function that takes 0-2 arguments: SPAN, if non-nil, and EXTRA, if non-nil.
RESPONSE-FN should be nil or a function that takes 2-4 arguments: the backend's response, SPAN, if non-nil, a boolean for if this is the original call (not a restoring one), and EXTRA, if non-nil. If SPAN is non-nil and you want something added to it, then return a dotted pair list (symbol . some-str).
SPAN should be a span. If non-nil, it will be passed to RESPONSE-FN/BATCH-FN and to Q-STR-OR-FN if it is a function.
You probably should not use IS-RESTORE.
HEADER should be a string that will be displayed in the header line.
EXTRA can be anything. If non-nil, it will be passed to RESPONSE-FN/BATCH-FN and to Q-STR-OR-FN if it is a function.
RESTORE should be t if you want this call re-done during batch processing.
DELAY should be non-nil if you want this to wait until the previous interactive call is finished to run."
  (let* ((span (se-get-span span))
	 (header (or header ""))
	 (q-str (cond
		 ((stringp q-str-or-fn) q-str-or-fn)
		 ((and span extra) (funcall q-str-or-fn span extra))
		 (span (funcall q-str-or-fn span))
		 (extra (funcall q-str-or-fn extra))
		 (t (funcall q-str-or-fn))))
	 (q (concat (se-inf-escape-string q-str) "\n"))
	 (closure (list q-str-or-fn response-fn (not is-restore) span extra restore (buffer-name))))
    (setq se-inf-interactive-running t)
    (se-inf-queue-header header)
    (tq-enqueue se-inf-queue q "\n" closure #'se-inf-interactive-response delay)))

(defun se-inf-interactive-response (closure response)
  "Receives a response from an `se-inf-interactive' call"
  (let ((q-str-or-fn (nth 0 closure))
	(response-fn (nth 1 closure))
	(oc (nth 2 closure)) ; Original Call
	(span (nth 3 closure))
	(extra (nth 4 closure))
	(restore (nth 5 closure))
	(buffer (nth 6 closure)))
    (with-current-buffer buffer
      (se-inf-next-header)
      (let* ((mod-fn (or se-inf-modify-response (lambda (response) response)))
	     (response (funcall mod-fn (se-inf-undo-escape-string response)))
	     (pair (cond
		    ((null response-fn) nil)
		    ((and span extra) (funcall response-fn response span oc extra))
		    (span (funcall response-fn response span oc))
		    (extra (funcall response-fn response oc extra))
		    (t (funcall response-fn response oc)))))
	(when (and span pair) (se-inf-add-to-span span pair)))
      (when restore
	(let ((restore-data (list q-str-or-fn response-fn extra))
	      (s (if span (se-span-start span) 1))
	      (e (if span (se-span-end span) 1)))
	  (se-inf-remove-dup-pin (se-pins-at s e 'se-interactive) restore-data)
	  (se-pin-data s e 'se-interactive restore-data)))
      (run-hooks 'se-inf-interactive-response-hook))))

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
	   (extra (nth 2 data))
	   (header (format "Recomputing interactive calls (%s/%s)" queued total)))
      (if span
	  (se-inf-interactive q-str-or-fn response-fn :span span :extra extra :header header :delay t :is-restore t)
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

(defun se-inf-process-response (response oc buffer)
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
     (message "%s" (error-message-string err)))))

(defun se-inf-parse-file (&optional file)
  "Sends parse request to current process.  Uses the current
buffer's file unless FILE is non-nil."
  (interactive)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (let ((ms (se-inf-get-message-from-filename (or file (se-inf-filename)))))
    (se-inf-interactive ms #'se-inf-process-response :extra (buffer-name) :header "Parsing")))

(defun se-inf-filename ()
  "Gets the filename of the current buffer (see `se-inf-filename')"
  (funcall se-inf-filename))

(defun se-inf-filename-base ()
  "Gets the filename base of the current buffer (see `se-inf-filename-base')"
  (funcall se-inf-filename-base (se-inf-filename)))

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

(defun se-inf-queue-header (str)
  "Adds str to  `se-inf-header-queue'"
  (if (string= str "")
      (setq se-inf-header-queue (append se-inf-header-queue (list "")))
    (let ((str (concat " " str " ")))
      (setq se-inf-header-queue (append se-inf-header-queue (list (vector (concat str "|") (concat str "/") (concat str "―") (concat str "\\")))))
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
