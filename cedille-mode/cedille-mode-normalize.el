;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;         Interactive Code         ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;        Commands        ;;;;;;;;

;(defun cedille-mode-elab-data (x)
;  (interactive "MName: ")
;  (call-interactively (lambda (x) (interactive "MParameters: ") (setq ps x)))
;  (call-interactively (lambda (x) (interactive "MIndices: ") (setq is x)))
;  (call-interactively (lambda (x) (interactive "MConstructors: ") (setq cs x)))
;  (setq encoding (if (y-or-n-p "Use Mendler encoding or simple Mendler encoding? ") "tt" "ff"))
;  (se-inf-interactive
;   (concat "interactive" cedille-mode-sep "data" cedille-mode-sep encoding cedille-mode-sep x cedille-mode-sep ps cedille-mode-sep is cedille-mode-sep cs)
;   cedille-mode-normalize-erase-receive-response-prompt
;   "" :header "Elaborating"))

(defun cedille-mode-normalize (&optional norm-method)
  "Normalizes either the selected span or a prompted expression"
  (interactive)
  (if se-mode-selected
      (cedille-mode-normalize-span (se-mode-selected) (or norm-method 'normalized))
    (cedille-mode-normalize-prompt (or norm-method 'normalized))))

(defun cedille-mode-head-normalize ()
  "Head-normalizes either the selected span or a prompted expression"
  (interactive)
  (cedille-mode-normalize 'head-normalized))

(defun cedille-mode-single-reduction ()
  "Performs a single reduction on either the selected span or a prompted expression"
  (interactive)
  (cedille-mode-normalize 'single-reduction))

(defun cedille-mode-erase ()
  "Erases either the selected span or a prompted expression"
  (interactive)
  (if se-mode-selected
      (cedille-mode-erase-span (se-mode-selected))
    (call-interactively
     (lambda (input)
       (interactive "MErase: ")
       (cedille-mode-erase-send-prompt input)))))
  

;;;;;;;;        Span Code        ;;;;;;;;

(defun cedille-mode-normalize-span(span norm-method)
  "Normalizes SPAN according to NORM-METHOD ('normalized, 'head-normalized, or 'single-reduction)"
  (let ((lang-level (cedille-mode-normalize-get-ll span)))
    (if (and lang-level (or (string= lang-level "term")
			    (string= lang-level "type")
			    (string= lang-level "kind")))
	(se-inf-interactive-with-span
	 'cedille-mode-normalize-request-text
	 cedille-mode-normalize-erase-receive-response
         norm-method
	 span
	 :header "Normalizing"
	 :restore cedille-mode-normalize-erase-receive-response-batch)
      (message "Node must be a term, type, or kind"))))

(defun cedille-mode-erase-span (span)
  "Erases span"
  (let ((lang-level (cedille-mode-normalize-get-ll span)))
    (if (and lang-level (string= lang-level "term"))
	(se-inf-interactive-with-span
	 'cedille-mode-erase-request-text
	 cedille-mode-normalize-erase-receive-response
	 'erased
         span
	 :header "Erasing"
	 :restore cedille-mode-normalize-erase-receive-response-batch)
      (message "Node must be a term"))))

(defun cedille-mode-normalize-erase-receive-response (response extra span)
  "Receives the text response from the backend and adds (symbol . response) to span."
  (add-hook 'se-inf-interactive-response-hook #'cedille-mode-normalize-inspect)
  (cons extra response))

(defun cedille-mode-normalize-request-text(extra span &optional add-to-pos) ; add-to-pos is for beta-reduction
  "Gets the text to send to the backend as a request to normalize a span"
  (cedille-mode-concat-sep
   "interactive"
   "normalize"
   (buffer-substring (se-span-start span) (se-span-end span))
   (cedille-mode-normalize-get-ll span)
   (number-to-string (+ (se-span-start span) (or add-to-pos 0)))
   (cedille-mode-norm-method-case extra "all" "head" "once")
   (cedille-mode-normalize-local-context-param span)))

(defun cedille-mode-erase-request-text(extra span)
  "Gets the text to send to the backend as a request to erase a span"
  (let ((s (se-span-start span))
	(e (se-span-end span)))
    (cedille-mode-erase-request-text-h (buffer-substring s e) (cedille-mode-normalize-get-ll span) s (cedille-mode-normalize-local-context-param span))))

(defun cedille-mode-erase-request-text-h (str ll pos lc-str)
  (cedille-mode-concat-sep "interactive" "erase" str ll (number-to-string pos) lc-str))

(defun cedille-mode-normalize-local-context-param(span)
  "Formats the local context into a string suitable to be sent to the backend"
  (let ((original-context (cedille-mode-span-context span)))
    (when original-context
      (cedille-mode-normalize-local-context-to-string (copy-tree original-context)))))

(defun cedille-mode-normalize-local-context-to-string(ctxt)
  "Converts CTXT into a string suitable to be sent to the backend"
  (let* ((terms (car ctxt));(cedille-mode-normalize-shadow-filter (car ctxt)))
	 (types (cdr ctxt));(cedille-mode-normalize-shadow-filter (cdr ctxt)))
	 out
;	 (split (lambda (item)
;		  (let ((loc (cdr (assoc 'location item)))
;			(del " - "))
;		    (when loc
;		      (let ((dash (string-match del loc)))
;			(when dash
;			  (cons (substring loc 0 dash) (substring loc (+ dash (length del))))))))))
         (mk (lambda (str l)
               (while l
                 (let* ((item (pop l))
                        ;(loc (funcall split item))
                        (fn (cdr (assoc 'fn item)))
                        (pos (cdr (assoc 'pos item)))
                        (value (cdr (assoc 'value item)))
                        (bv (or (cdr (assoc 'bound-value item)) "")))
                   (if out
                       (setq out (cedille-mode-concat-sep out str (car item) bv value fn pos))
                     (setq out (cedille-mode-concat-sep str (car item) bv value fn pos))))))))
    (funcall mk "term" terms)
    (funcall mk "type" types)
    (or out "")))

(defun cedille-mode-normalize-shadow-filter(lst)
  (let (shadowed-lst)
    (dolist (pair (reverse lst) shadowed-lst)
      (let* ((symbol (car pair)) (matches (lambda (thispair) (equal (car thispair) symbol))))
	(setq shadowed-lst (cons pair (remove-if matches shadowed-lst)))))
    shadowed-lst))

(defun cedille-mode-normalize-get-ll (term)
  "Returns the language level of TERM"
  (cdr (assoc 'language-level (se-term-data term))))

(defun cedille-mode-normalize-inspect ()
  "Updates the inspect buffer and opens it if it is closed"
  (remove-hook 'se-inf-interactive-response-hook #'cedille-mode-normalize-inspect)
  (when (not se-inf-interactive-running)
    (let ((buffer (cedille-mode-inspect-buffer)))
      (with-current-buffer buffer
	(display-buffer buffer))
      (cedille-mode-inspect))))




;;;;;;;;        Prompt Code        ;;;;;;;;

(defun cedille-mode-normalize-prompt (&optional norm-method)
  "Prompts the user to input an expression to normalize/head-normalize"
  (call-interactively
   `(lambda (input)
      (interactive ,(cedille-mode-norm-method-case norm-method "MNormalize: " "MHead-normalize" "MReduce: "))
      (cedille-mode-normalize-send-prompt input ',norm-method))))

(defun cedille-mode-normalize-send-prompt (input norm-method)
  "Sends the prompted normalize request to the backend"
  (se-inf-interactive
   (cedille-mode-concat-sep
    "interactive"
    "normalizePrompt"
    input
    (cedille-mode-norm-method-case norm-method "all" "head" "once")
    (cedille-mode-normalize-local-context-to-string cedille-mode-global-context))
   cedille-mode-normalize-erase-receive-response-prompt
   (concat "Expression: " input "\n"
           (cedille-mode-norm-method-case
            norm-method "Normalized: " "Head-normalized: " "Single-reduction: " ))
   :header "Normalizing"))

(defun cedille-mode-erase-send-prompt (input)
  (se-inf-interactive
   (cedille-mode-concat-sep
    "interactive"
    "erasePrompt"
    input
    (cedille-mode-normalize-local-context-to-string cedille-mode-global-context))
   cedille-mode-normalize-erase-receive-response-prompt
   (concat "Expression: " input "\nErased: ")
   :header "Erasing"))

;;;;;;;;        Helpers        ;;;;;;;;

(defun cedille-mode-norm-method-case (norm-method all head once)
  (cond
   ((eq 'normalized norm-method) all)
   ((eq 'head-normalized norm-method) head)
   ((eq 'single-reduction norm-method) once)))

(defmacro cedille-mode-response-macro (fn &optional suppress-err)
  `(lambda (response extra &optional span)
     (cedille-mode-response ,fn response extra span ,suppress-err)))

(defvar cedille-mode-normalize-erase-receive-response-prompt
  (cedille-mode-response-macro
   (lambda (response extra)
     (cedille-mode-scratch-insert-text (concat extra response)))))

(defvar cedille-mode-normalize-erase-receive-response
  (cedille-mode-response-macro
   (lambda (response extra span)
     (progn
       (add-hook 'se-inf-interactive-response-hook #'cedille-mode-normalize-inspect)
       (cons extra response)))))

(defvar cedille-mode-normalize-erase-receive-response-batch
  (cedille-mode-response-macro
   (lambda (response extra span)
     (cons extra response))))

(defun cedille-mode-str-is-var (str)
  "Returns t if STR is a variable"
  (not (string-match " " str)))

(defun cedille-mode-response (fn response extra span suppress-err)
  "Wrapper function that turns RESPONSE into a json, propertizes it, and passes it to FN along with EXTRA and SPAN (if non-nil)"
  (let* ((json-array-type 'list)
         (json (json-read-from-string response))
         (ls (cdr (assoc 'value json)))
         (err (cdr (assoc 'error json)))
         (val (cadr ls))
         (ts (caddr ls))
         (str (cedille-mode-apply-tags val ts)))
    (if err
        (unless suppress-err (message err))
      (if span
          (funcall fn str extra span)
        (funcall fn str extra)))))

(provide 'cedille-mode-normalize)
