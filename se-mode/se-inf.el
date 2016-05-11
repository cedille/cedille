
(require 'tq)
(require 'json)

(eval-when-compile (require 'cl))

(make-variable-buffer-local
 (defvar se-inf-process nil
   "Holds process for current buffer in se-mode.  Processes are
started with `start-process'."))

(make-variable-buffer-local
 (defvar se-inf-queue nil
   "Transaction queue for `se-inf-process'."))

(defvar se-inf-response-hook
  (list #'se-inf-process-spans
	#'se-inf-process-error
	#'se-inf-process-error-span)
  "Functions to be evaluated after response of `se-inf-ask',
response given as only argument.  If `se-inf-response-is-json' is
non-nil the response is parsed as JSON first.")

(make-variable-buffer-local
 (defvar se-inf-response-finished nil
   "Set to true after a response has been recieved and
`se-inf-response-hook' is executed."))

(defvar se-inf-parse-hook (list #'se-inf-save-if-modified #'se-inf-remove-overlays)
  "Functions to be evaluated before parse request.")

(make-variable-buffer-local
 (defvar se-inf-response-is-json t
   "Non-nil if `se-inf-process' should returns JSON.  See
`se-inf-response-hook'."))

(defvar se-inf-headers
  (vector " Parsing |" " Parsing /" " Parsing -" " Parsing \\")
  "A loop of strings to show while parsing is happening in the
background.  Suppose to be similar to a hourglass.")

(make-variable-buffer-local
 (defvar se-inf-header-index 0
   "Current index of the header loop."))

(defvar se-inf-header-line-format
  '(:eval (aref se-inf-headers (mod se-inf-header-index 4)))
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
  (unless (process-get proc 'se-inf-queue)
    (process-put proc 'se-inf-queue (tq-create proc))
    (process-put proc 'se-inf-auto-kill (not no-auto-kill)))
  (setq
   se-inf-process proc
   se-inf-queue (process-get proc 'se-inf-queue)))

(defun se-inf-stop ()
  "Should be called at the end of an `se-mode' session.  This
will kill the process, should be skipped if process is shared."
  (tq-close se-inf-queue)
  (kill-buffer (tq-buffer se-inf-queue)))

(defun se-inf-ask (question &optional fn)
  "Send a message to the current `se-inf-process'.  Question will
be terminated with a new line. Calls FN or
`se-inf-process-response' when a one line response is returned."
  (unless (string-suffix-p "\n" question)
    (setq question (concat question "\n")))
  (tq-enqueue se-inf-queue question "\n" (buffer-name) (or fn #'se-inf-process-response)))

(defun se-inf-process-response (closure response)
  "Called to evaluate `se-inf-response-hook' upon response from
`se-inf-process'."
  (condition-case err
      (with-current-buffer closure
	(unwind-protect
	    (if se-inf-response-is-json
		(let* ((json-array-type 'list)
		       (json (json-read-from-string response)))
		  (run-hook-with-args 'se-inf-response-hook json))
	      (run-hook-with-args 'se-inf-response-hook response))
	  (se-inf-header-timer-stop)
	  (setq se-inf-response-finished t)))
    (error
     (message "%s" (error-message-string err)))))

(defun se-inf-parse-file (&rest file)
  "Sends parse request to current process.  Sends the default
request unless `se-inf-parse-hook' is non-nil.  Uses the current
buffer's file unless FILE is non-nil."
  (interactive)
  (se-inf-header-timer-start)
  (run-hooks 'se-inf-parse-hook)
  (setq se-inf-response-finished nil)
  (se-inf-ask (or file (buffer-file-name))))

(defun se-inf-save-if-modified ()
  "Save the buffer only if it is modified."
  (interactive)
  (when (buffer-modified-p)
    (save-buffer)))

(defun se-inf-get-spans (json)
  "Returns spans from default formatted JSON."
  (cdr (assoc 'spans json)))

(defun se-inf-process-spans (json)
  "Creates parse tree from spans found in JSON. Sets the variable
`se-mode-parse-tree'."
  (when (se-inf-get-spans json)
    (setq se-mode-parse-tree
	  (se-create-parse-tree
	   (se-create-spans
	    (se-inf-get-spans json))))))

(defun se-inf-get-error (json)
  "Returns possible error from default formatted JSON."
  (cdr (assoc 'error json)))

(defun se-inf-process-error (json)
  "Displays error message found in JSON."
  (let ((msg (se-inf-get-error json)))
    (when msg
      (message "Error: %s" msg))))

(defun se-inf-get-error-span (json)
  "Returns possible error spans from default formatted JSON."
  (let ((data (cdr (assoc 'error-span json))))
    (cond
     ((or (null data)
	  (< (length data) 3))
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
  (remove-overlays (point-min) (point-max)))

(defun se-inf-error-overlay (span)
  "Creates an overlay over SPAN to indicate an error."
  (let ((overlay (make-overlay (se-term-start span)
			       (se-term-end span))))
    (overlay-put overlay 'info (se-span-data (se-first-span span)))
    (overlay-put overlay 'face "error")
    (overlay-put overlay 'modification-hooks
		 (list (lambda (overlay &rest args)
			 (overlay-put overlay 'face nil))))))

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

(provide 'se-inf)
