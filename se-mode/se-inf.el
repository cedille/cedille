(require 'tq)
(require 'json)

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
 (defvar se-inf-response-is-json t
   "Non-nil if `se-inf-process' should return JSON.  See
`se-inf-response-hook'."))

(defvar se-inf-parsing-headers
  (vector " Parsing |" " Parsing /" " Parsing -" " Parsing \\")
  "A loop of strings to show while parsing is happening in the
background. Supposed to be similar to an hourglass.")

(make-variable-buffer-local
 (defvar se-inf-header-queue nil
   "The queue of header strings to show for consecutive interactive calls"))

(make-variable-buffer-local
 (defvar se-inf-headers se-inf-parsing-headers))

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

(defun se-inf-set-header-format ()
  (setq se-inf-header-line-format '(:eval (aref se-inf-headers (mod se-inf-header-index 4)))))

(defun se-inf-queue-header (str)
  "Adds str to  `se-inf-header-queue'"
  (setq str (concat " " str))
  (setq se-inf-header-queue (append se-inf-header-queue (list (vector (concat str " |") (concat str " /") (concat str " -") (concat str " \\")))))
  (unless header-line-format (se-inf-next-header)))

(defun se-inf-next-header ()
  "If `header-line-format' is nil, then sets it to be the first element from `se-inf-header-queue', which gets popped"
  (setq popped (pop se-inf-header-queue))
  (if (null popped)
      (se-inf-finish-response)
      (setq se-inf-headers popped)
      (se-inf-set-header-format)
      (se-inf-header-timer-start)))

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
  (kill-buffer (tq-buffer se-inf-queue))
  (when (car se-inf-queue)
    (setq se-inf-header-queue nil)
    (setq se-inf-headers se-inf-parsing-headers)
    (setq header-line-format nil)
    (setq current (nth 1 (cdr (car (car se-inf-queue)))))
    (setq symbol (nth 0 current))
    (setq span (nth 1 current))
    (setq pins (se-pins-at (se-span-start span) (se-span-end span) 'se-interactive))
    (setq pins (se-inf-filter-pins-symbol symbol pins '()))
    (se-unpin-list pins)))

(defun se-inf-filter-pins-symbol (symbol pins so-far)
  "Filters out pins without symbol"
  (if (null pins)
      so-far
      (setq h (car pins))
      (setq symbol2 (car (se-pin-item-data h)))
      (when (equal symbol symbol2) (setq so-far (cons h so-far)))
      (se-inf-filter-pins-symbol symbol (cdr pins) so-far)))

(cl-defun se-inf-interactive (q-str-or-fn response-fn &key span batch-fn header q-arg symbol response-split-fn add-to-span pin)
  "Sends an interactive request to the backend.
Q-STR-OR-FN should be either a string or a function that takes SPAN and Q-ARG as arguments and returns a string. It determines what string will be sent to the backend.
RESPONSE-FN should be a function that takes three arguments: SPAN, response, and extra data. Unless RESPONSE-SPLIT-FN is specified, extra data will be nil.
SPAN should be a span.
BATCH-FN should be like RESPONSE-FN. If specified, it will be called during batch processing instead of RESPONSE-FN (that is, if PIN is non-nil).
HEADER should be a string to show as a header until the response is received.
Q-ARG can be anything. It will be passed as an argument to a function Q-STR-OR-FN.
SYMBOL should be given only if ADD-TO-SPAN is as well. It determines what the key to the pair added to SPAN will be.
RESPONSE-SPLIT-FN, if specified, should be a function with a single argument: the backend's response. It should return a dotted pair. The first element will be passed as response to RESPONSE-FN/BATCH-FN; the second as extra data.
ADD-TO-SPAN should be non-nil if you want (symbol . response) to be added to the 'se-interactive value of span.
PIN should be non-nil if you want this to be called again during batch processing."
  (when span (setq span (se-first-span span)))
  (setq q (concat (se-inf-escape-string (if (stringp q-str-or-fn) q-str-or-fn (funcall q-str-or-fn span q-arg))) "\n"))
  (setq closure (list symbol span q-str-or-fn q-arg response-fn batch-fn response-split-fn add-to-span pin (buffer-name)))
  (when header (se-inf-queue-header header))
  (tq-enqueue se-inf-queue q "\n" closure #'se-inf-interactive-response))

(defun se-inf-interactive-response (closure response)
  "Receives a response from an `se-inf-interactive' call"
  (let* ((response (se-inf-undo-escape-string response))
	 (symbol (nth 0 closure))
	 (span (nth 1 closure))
	 (q-str-or-fn (nth 2 closure))
	 (q-arg (nth 3 closure))
	 (response-fn (nth 4 closure))
	 (batch-fn (nth 5 closure))
	 (response-split-fn (nth 6 closure))
	 (add-to-span (nth 7 closure))
	 (pin (nth 8 closure))
	 (buffer (nth 9 closure))
	 (r-pair (if response-split-fn (response-split-fn response) (cons response "")))
	 (r-text (car r-pair))
	 (r-extra (cdr r-pair)))
    (with-current-buffer buffer
      (se-inf-next-header)
      (when span
	(when pin
	  (setq pin-data (list symbol (or batch-fn response-fn) q-str-or-fn q-arg add-to-span response-split-fn))
	  (setq start (se-span-start span))
	  (setq end (se-span-end span))
	  (se-inf-remove-dup-pin (se-pins-at start end 'se-interactive) pin-data)
	  (se-pin-data (se-span-start span) (se-span-end span) 'se-interactive pin-data))
	(when (and symbol add-to-span)
	  (se-inf-add-to-span span r-text symbol)))
      (funcall response-fn span r-text r-extra))))
      ;(unless se-inf-interactive-restored
;	(se-inf-inc-current)))))

(defun se-inf-add-to-span (span text symbol)
  "Adds text to list of span's interactive properties in form of list/pair: (symbol . text)"
  (setq data (se-span-data span))
  (setq int (cdr (assoc 'se-interactive data)))
  (setq int (se-inf-add-to-span-h int nil text symbol))
  (setq new (se-inf-add-to-span-h data nil int 'se-interactive))
  (setf (se-span-data span) new))

(defun se-inf-add-to-span-h (data result text symbol)
  "Adds item to data, removing all other occurences of symbol"
  (if (null data)
      (reverse (cons (cons symbol text) result))
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

(defun se-inf-run-pins(pins queued total)
  "Recursively iterates through pins and calls each function with its args (span and question)"
  (when pins
    (let* ((h (car pins))
	   (data (se-pin-item-data h))
	   (start (se-pin-item-start h))
	   (end (se-pin-item-end h))
	   (span (se-span-from start end))
	   (symbol (nth 0 data))
	   (response-fn (nth 1 data))
	   (q-str-or-fn (nth 2 data))
	   (q-arg (nth 3 data))
	   (add-to-span (nth 4 data))
	   (response-split-fn (nth 5 data)))
      (if span
	  (se-inf-interactive q-str-or-fn response-fn :span span :q-arg q-arg :symbol symbol :response-split-fn response-split-fn :add-to-span add-to-span :header (format "Restoring interactive calls (%s/%s)" queued total))
	  (se-unpin h))
	  ;(se-inf-inc-current))
      (se-inf-run-pins (cdr pins) (+ 1 queued) total))))

(defun se-inf-restore-interactive ()
  "Restores interactive calls"
  (setq pins (se-get-pins 'se-interactive))
  (if pins
      (se-inf-run-pins pins 0 (length pins))
      (se-inf-finish-response)))

(defun se-inf-finish-response ()
  "Stops the header timer, sets `se-inf-response-finished' to t, resets the header, etc..."
  (se-inf-header-timer-stop)
  (setq se-inf-headers se-inf-parsing-headers)
  (setq se-inf-interactive-restored t))

;(defun se-inf-clear-interactive-all ()
;  "Clears all interactive pins. Called by typing C-I."
;  (interactive)
;  (se-pin-clear-all 'se-interactive)
;  (se-mapc 'se-inf-clear-span-interactive (se-mode-parse-tree)))

(defun se-inf-clear-span-interactive (span)
  "Clears the interactive properties from span"
  (assq-delete-all 'se-interactive (se-span-data span)))

;(defun se-inf-clear-interactive ()
;  "Clears all interactive pins associated with the current span. Called by typing C-i."
;  (interactive)
;  (when se-mode-selected
;    (setq span (se-first-span (se-mode-selected)))
;    (setq s (se-span-start span))
;    (setq e (se-span-end span))
;    (se-unpin-list (se-pins-at s e 'se-interactive))
;    (se-inf-clear-span-interactive span)))
;    ;(when se-mode-selected
;    ;  (message "se-mode-selected2 t")
;    ;  (se-mode-select se-mode-selected))))

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
	  (setq header-line-format nil)
	  (se-inf-header-timer-stop)
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
