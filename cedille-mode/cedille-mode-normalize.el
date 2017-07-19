(load-library "cedille-mode-parent")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;          Normalize Code          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defvar sep "§")
(defvar sep2 "⦀")


(defun cedille-mode-normalize()
  "Normalizes either the currently selected span or a prompted expression"
  (interactive)
  (if se-mode-selected
      (cedille-mode-normalize-span (se-mode-selected))
      (cedille-mode-normalize-prompt nil)))

(defun cedille-mode-normalize-full()
  "Normalizes either the currently selected span or a prompted expression completely"
  (interactive)
  (if se-mode-selected
      (cedille-mode-normalize-span (se-mode-selected) t)
      (cedille-mode-normalize-prompt t)))

(defun cedille-mode-normalize-span(span &optional full)
  "Normalizes span"
  (setq lang-level (cdr (assoc 'language-level (se-term-data span))))
  (setq fn (if full 'cedille-mode-normalize-receive-full-response 'cedille-mode-normalize-receive-response))
  (setq symbol (if full 'normalized 'head-normalized))
  (if (and lang-level (or (string= lang-level "term") (string= lang-level "type")))
      (se-inf-interactive 'cedille-mode-normalize-request-text fn :span span :q-arg (list lang-level full) :symbol symbol :add-to-span t :pin t :header "Normalizing")
      (message "Selected span must be a term or a type")))


;;;;;;;;       Span Code       ;;;;;;;;


(defun cedille-mode-normalize-request-text(span rest)
  "Gets the text to send to the backend as a request to normalize a span"
  (setq lang-level (car rest))
  (setq full (nth 1 rest))
  (setq s (se-span-start span))
  (setq e (se-span-end span))
  (concat "normalize"
	  sep (format "%s" s)
	  sep (buffer-substring-no-properties s e)
	  sep lang-level
	  sep (file-truename (buffer-file-name))
	  sep (if full "tt" "ff")
	  (cedille-mode-normalize-local-context-param span)))

(defun cedille-mode-normalize-local-context-param(span)
  "Formats the local context into a string suitable to be sent to the backend"
  (let ((original-context (cedille-mode-span-context span))
	(out ""))
    (when original-context
      (let* ((ctxt (copy-tree original-context))
	     (terms (cedille-mode-normalize-shadow-filter (car ctxt)))
	     (types (cedille-mode-normalize-shadow-filter (cdr ctxt))))
        (while terms
          (setq item (pop terms))
          (setq out (concat out sep "term" sep2 (car item) sep2 (cdr (assoc 'value item)))))
	(while types
	  (setq item (pop types))
	  (setq out (concat out sep "type" sep2 (car item) sep2 (cdr (assoc 'value item)))))))
    out))

(defun cedille-mode-normalize-shadow-filter(lst)
  (let (shadowed-lst)
    (dolist (pair (reverse lst) shadowed-lst)
      (let* ((symbol (car pair)) (matches (lambda (thispair) (equal (car thispair) symbol))))
	(setq shadowed-lst (cons pair (remove-if matches shadowed-lst)))))
    shadowed-lst))

(defun cedille-mode-normalize-receive-full-response (span response nilvar)
  ""
  (cedille-mode-normalize-erase-receive-response 'normalized span response))

(defun cedille-mode-normalize-receive-response (span response nilvar)
  "Receives the normalize text response from the backend. Handler for when the user requested a span to be normalized."
  (cedille-mode-normalize-erase-receive-response 'head-normalized span response))

(defun cedille-mode-normalize-erase-receive-response (symbol span response)
  "Receives the text response from the backend and adds (symbol . response) to span."
  (cedille-mode-normalize-inspect span)
  (cedille-mode-rebalance-windows))

(defun cedille-mode-normalize-inspect (span)
  "Updates the inspect buffer and opens it if it is closed"
  (when (eq span (se-first-span (se-mode-selected)))
    (display-buffer (cedille-mode-inspect-buffer)))
  (cedille-mode-inspect))




;;;;;;;;       Prompt Code       ;;;;;;;;


;(defun cedille-mode-display-normalize-text(buffer text)
;  "Displays text in given buffer"
;  (with-current-buffer (cedille-mode-normalize-buffer)
;    (setq buffer-read-only nil)
;    (setq buffer-text (buffer-string))
;    (erase-buffer)
;    (if (string= buffer-text "")
;	(insert text)
;      (insert text "\n\n" buffer-text))
;    (setq buffer-read-only t)
;    (display-buffer (cedille-mode-normalize-buffer-name))
;    (cedille-mode-normalize-rebalance-window (get-buffer-window) text)))

;(defun cedille-mode-normalize-buffer-name()
;  "*cedille-normalize-erase*")

;(defun cedille-mode-normalize-buffer()
;  "Creates or gets the normalize buffer"
;  (get-buffer-create (cedille-mode-normalize-buffer-name)))

;(defun cedille-mode-normalize-rebalance-window(win text)
;  "Rebalances the normalize window size"
;  (with-selected-window win
;    (setq width (window-body-width))
;    (setq height (window-body-height))
;    (setq len (length text))
;    (setq newlines (count-lines 1 len))
;    (setq lines (+ newlines (/ (- len newlines) width)))
;    (setq delta (- lines height))
;    (enlarge-window delta)))

(defun cedille-mode-normalize-prompt (full)
  "Prompts the user to input an expression to normalize"
  (setq input (call-interactively (if full 'cedille-mode-normalize-full-open-prompt 'cedille-mode-normalize-open-prompt)))
  (se-inf-interactive (concat "normalizePrompt" sep input sep (if full "tt" "ff")) 'cedille-mode-normalize-receive-response-prompt :header "Normalizing"))

(defun cedille-mode-normalize-receive-response-prompt(nilvar1 text &optional nilvar2)
  "Receives the normalize text response (or error text) from the backend. Handler for when the user typed an expression into the prompt."
  (cedille-mode-scratch-display-text (se-inf-undo-escape-string text)))
  ;(cedille-mode-display-normalize-text (cedille-mode-normalize-buffer) (se-inf-undo-escape-string text)))

(defun cedille-mode-normalize-open-prompt (text)
  (interactive "MHead-normalize: ")
  text)

(defun cedille-mode-normalize-full-open-prompt (text)
  (interactive "MNormalize: ")
  text)


;;; Erasure ;;;

(defun cedille-mode-erase ()
  "Erases either the currently selected span or a prompted expression"
  (interactive)
  (if se-mode-selected
      (cedille-mode-erase-span (se-mode-selected))
      (call-interactively 'cedille-mode-erase-prompt)))

(defun cedille-mode-erase-prompt (input)
  (interactive "MErase: ")
  (se-inf-interactive (concat "erasePrompt" sep input) 'cedille-mode-normalize-receive-response-prompt :header "Erasing"))

(defun cedille-mode-erase-span (span)
  "Erases span"
  (setq lang-level (cdr (assoc 'language-level (se-term-data span))))
  (if (and lang-level (string= lang-level "term"))
      (se-inf-interactive 'cedille-mode-erase-request-text 'cedille-mode-erase-receive-response :span span :symbol 'erased :add-to-span t :pin t :header "Erasing")
      (message "Selected span must be a term")))

(defun cedille-mode-erase-request-text(span nilvar)
  "Gets the text to send to the backend as a request to normalize a span"
  (setq s (se-span-start span))
  (setq e (se-span-end span))
  (concat "erase"
	  sep (format "%s" s)
	  sep (buffer-substring-no-properties s e)
	  sep (file-truename (buffer-file-name))
	  (cedille-mode-normalize-local-context-param span)))

(defun cedille-mode-erase-receive-response (span response nilvar)
  "Receives the erasure text response from the backend. Handler for when the user requested a span to be erased."
  (cedille-mode-normalize-erase-receive-response 'erased span response))

(provide 'cedille-mode-normalize)
