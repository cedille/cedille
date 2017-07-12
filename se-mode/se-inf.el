
(require 'tq)
(require 'json)
;(require 'se-pin) ; Is this import necessary?

(eval-when-compile (require 'cl))

(make-variable-buffer-local
 (defvar se-inf-process-every-other nil
   "A simple way to avoid batch processing twice until the source of the bug is found"))

(make-variable-buffer-local
 (defvar se-inf-process nil
   "Holds process for current buffer in se-mode.  Processes are
started with `start-process'."))

(make-variable-buffer-local
  (defvar se-inf-json nil "The direct result of reading the JSON from the backend (for debugging)."))

(make-variable-buffer-local
 (defvar se-inf-queue nil
   "Transaction queue for `se-inf-process'."))

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
   "Set to true after a response has been received and
`se-inf-response-hook' is executed."))

(make-variable-buffer-local
 (defvar se-inf-interactive-restored nil))

(defvar se-inf-parse-hook (list #'se-inf-save-if-modified #'se-inf-remove-overlays)
  "Functions to be evaluated before parse request.")

(make-variable-buffer-local
 (defvar se-inf-interactive-calls-current nil))

(make-variable-buffer-local
 (defvar se-inf-interactive-calls-total nil))

(make-variable-buffer-local
 (defvar se-inf-response-is-json t
   "Non-nil if `se-inf-process' should return JSON.  See
`se-inf-response-hook'."))

(defvar se-inf-parsing-headers
  (vector " Parsing |" " Parsing /" " Parsing -" " Parsing \\")
  "A loop of strings to show while parsing is happening in the
background. Supposed to be similar to an hourglass.")

(make-variable-buffer-local
 (defvar se-inf-interactive-headers nil))
   ;(vector " Error |" " Error /" " Error -" " Error \\")
   ;"A loop of strings to show while interactive calls are being re-processed in the background. Supposed to be similar to an hourglass."))

(make-variable-buffer-local
 (defvar se-inf-headers se-inf-parsing-headers))
;  (vector " Parsing |" " Parsing /" " Parsing -" " Parsing \\")
;  "A loop of strings to show while parsing is happening in the
;background. Supposed to be similar to an hourglass.")

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

(defun se-inf-generate-headers (str)
  "Sets `se-inf-headers' to be a generated vector based on str"
  (setq str (concat " " str))
  (setq se-inf-headers (vector (concat str " |") (concat str " /") (concat str " -") (concat str " \\"))))

(defun se-inf-update-interactive-headers ()
  "Sets `se-inf-interactive-headers' to reflect current progress"
  (setq header-is-interactive nil)
  (when (eq se-inf-headers se-inf-interactive-headers) (setq header-is-interactive t))
  (setq str (format " Restoring interactive calls (%s/%s) " se-inf-interactive-calls-current se-inf-interactive-calls-total))
  (setq se-inf-interactive-headers (vector (concat str "|") (concat str "/") (concat str "-") (concat str "\\")))
  (when header-is-interactive (setq se-inf-headers se-inf-interactive-headers)))

(defun se-inf-start (proc &optional no-auto-kill)
  "Initialize necessary variables to use se-inf functions.
Expects PROC to be the process returned from `start-process'.
Should be called at the start of an `se-mode'.

When NO-AUTO-KILL is nil the user will not be queried about PROC
still being active upon exiting emacs."
  (with-silent-modifications
    (se-inf-put-remove-interactive-property 1 (length (buffer-string))))
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

(defun se-inf-interactive (question-fn span fn batch-fn question-args &optional header-str)
  "Sends an interactive call to the backend. Upon receiving a response, fn will be called with span and the response. If symbol or span are nil, the interactive call will not be pinned to the text. If batch-fn is not nil, it will be called when during batch processing; if it is nil, fn will be used. question-fn should take a span and a list argument (question-args)"
  (setq span (se-mode-ensure-span span))
  (setq question (funcall question-fn span question-args))
  (setq s (se-span-start span))
  (setq e (se-span-end span))
  (setq q (format "interactive§%s§%s§%s§%s" s e (buffer-substring-no-properties s e) question))
  (setq q (concat (se-inf-escape-string q) "\n"))
  (when header-str
    (se-inf-generate-headers header-str)
    (se-inf-header-timer-start))
  (tq-enqueue se-inf-queue q "\n" (list fn (buffer-name) span question-fn batch-fn question-args) #'se-inf-interactive-response))

(defun se-inf-interactive-response (closure response)
  "Receives a response from an `se-inf-interactive' call"
  (setq response (se-inf-undo-escape-string response))
  (setq buffer (nth 1 closure))
  (with-current-buffer buffer
    (when se-inf-interactive-restored (se-inf-header-timer-stop))
    (let ((fn (nth 0 closure))
	  (span (nth 2 closure))
	  (question-fn (nth 3 closure))
	  (batch-fn (nth 4 closure))
	  (question-args (nth 5 closure)))
      (if batch-fn
	  (setq pin-data (list batch-fn question-fn question-args))
	  (setq pin-data (list fn question-fn question-args)))
      (when span
	(setq start (se-span-start span))
	(setq end (se-span-end span))
	(se-inf-remove-dup-pin (se-pins-at start end 'se-interactive) pin-data)
	(se-pin-data (se-span-start span) (se-span-end span) 'se-interactive pin-data))
      (funcall fn span response))
    (unless se-inf-interactive-restored
      (se-inf-inc-current))))

(defun se-inf-add-to-span (span text symbol)
  "Adds text to span in form of list: (symbol . text)"
  (setq data (se-span-data span))
  (setq int (cdr (assoc 'se-interactive data)))
  (setq int (se-inf-add-to-span-h int nil text symbol))
  (setq new (se-inf-add-to-span-h data nil int 'se-interactive))
  (setf (se-span-data span) new))

(defun se-inf-add-to-span-h (data result text symbol)
  "Adds item to data, removing all other occurences of symbol"
  (if (null data)
      (rev (cons `(,symbol . ,text) result))
      (setq h (car data))
      (unless (equal (car h) symbol)
	(setq result (cons h result)))
      (se-inf-add-to-span-h (cdr data) result text symbol)))

(defun se-inf-remove-dup-pin (pins data)
  "Removes duplicate 'se-interactive pin so that repeated calls to the same span won't be needlessly done again during re-processing"
  (when pins
    (setq h (car pins))
    (if (equal data (se-pin-item-data h))
        (se-unpin h) ; No need to go further
        (se-inf-remove-dup-pin (cdr pins) data))))

(defun se-inf-inc-current ()
   "Increments `se-inf-interactive-calls-current'"
  (unless se-inf-interactive-calls-current
    (setq se-inf-interactive-calls-current 0))
  (incf se-inf-interactive-calls-current)
  ;(message "%s/%s" se-inf-interactive-calls-current se-inf-interactive-calls-total)
  (if (equal se-inf-interactive-calls-current se-inf-interactive-calls-total)
      (se-inf-finish-response)
      (se-inf-update-interactive-headers)))

(defun se-inf-run-pins(pins)
  "Recursively iterates through pins and calls each function with its args (span and question)"
  (when pins
    (let* ((h (car pins))
	   (data (se-pin-item-data h))
	   (start (se-pin-item-start h))
	   (end (se-pin-item-end h))
	   (span (se-span-from start end))
	   (fn (nth 0 data))
	   (question-fn (nth 1 data))
	   (question-args (nth 2 data)))
      (if span
	  (se-inf-interactive question-fn span fn nil question-args)
	  (se-unpin h)
	  (se-inf-inc-current))
      (se-inf-run-pins (cdr pins)))))

(defun se-inf-restore-interactive ()
  "Restores interactive calls"
  (setq pins (se-get-pins 'se-interactive))
  (setq se-inf-interactive-calls-current 0)
  (setq se-inf-interactive-calls-total (length pins))
  (se-inf-update-interactive-headers)
  (if pins
      (se-inf-run-pins pins)
      (se-inf-finish-response)))

(defun se-inf-finish-response ()
  "Stops the header timer, sets `se-inf-response-finished' to t, resets the header, etc..."
  (se-inf-header-timer-stop)
  (setq se-inf-headers se-inf-parsing-headers)
  (setq se-inf-interactive-restored t)
  (setq se-inf-interactive-calls-current nil)
  (setq se-inf-interactive-calls-total nil))

(defun se-inf-clear-interactive ()
  "Clears all interactive pins. Called by typing C-i."
  (interactive)
  (se-pin-clear-all 'se-interactive))

(defun se-inf-ask (question &optional fn)
  "Send a message to the current `se-inf-process'.  Question will
be terminated with a new line. Calls FN or
`se-inf-process-response' when a one line response is returned."
  (setq question (se-inf-escape-string question))
  ;(unless (string-suffix-p "\n" question)
  (setq question (concat question "\n"))
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
                  (setq se-inf-json json)
		  (run-hook-with-args 'se-inf-response-hook json))
	      (run-hook-with-args 'se-inf-response-hook response))
	  (setq se-inf-headers se-inf-interactive-headers)
	  (se-inf-restore-interactive)
	  (setq se-inf-response-finished t)))
    (error
     (message "%s" (error-message-string err)))))

(defun se-inf-parse-file (&rest file)
  "Sends parse request to current process.  Uses the current
buffer's file unless FILE is non-nil."
  (interactive)
  (setq se-inf-process-every-other (not se-inf-process-every-other))
  (when se-inf-process-every-other
    (se-inf-header-timer-start)
    (run-hooks 'se-inf-parse-hook)
    (setq se-inf-response-finished nil)
    (setq se-inf-interactive-restored nil)
    (se-inf-ask (funcall se-inf-get-message-from-filename (or file (buffer-file-name))))))

(defun se-inf-save-if-modified ()
  "Save the buffer only if it is modified."
  (interactive)
  (when (buffer-modified-p)
    (save-buffer)))

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

(defun se-inf-put-remove-interactive-property (start end)
  "Puts the text property 'insert-in-front-hooks to the range from start to end, with the value being `se-inf-remove-interactive-props'"
  ; This clears all former 'insert-in-front-hooks properties,
  ; but this will have no consequence since the text is inserted
  ; and this property shouldn't matter on fresh text
  (put-text-property start end 'insert-in-front-hooks (list #'se-inf-remove-interactive-props)))

(defun se-inf-remove-interactive-props (start end)
  "Removes se-interactive properties from inserted text if it was pasted"
  (put-text-property start end 'se-pin nil)
  (se-inf-put-remove-interactive-property start end))

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

(provide 'se-inf)
