(load-library "cedille-mode-parent")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;          Normalize Code          ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defvar sep "§")
(defvar sep2 "⦀")


;;;;;;;;        Commands        ;;;;;;;;

(defun cedille-mode-normalize()
  "Normalizes either the currently selected span or a prompted expression"
  (interactive)
  (if se-mode-selected
      (cedille-mode-normalize-span (se-mode-selected) nil)
      (cedille-mode-normalize-prompt nil)))

(defun cedille-mode-normalize-full()
  "Normalizes either the currently selected span or a prompted expression completely"
  (interactive)
  (if se-mode-selected
      (cedille-mode-normalize-span (se-mode-selected) t)
      (cedille-mode-normalize-prompt t)))

(defun cedille-mode-erase ()
  "Erases either the currently selected span or a prompted expression"
  (interactive)
  (if se-mode-selected
      (cedille-mode-erase-span (se-mode-selected))
      (call-interactively 'cedille-mode-erase-prompt)))


;;;;;;;;        Span Code        ;;;;;;;;

(defun cedille-mode-normalize-span(span full)
  "Normalizes span"
  (setq lang-level (cdr (assoc 'language-level (se-term-data span))))
  (setq fn (if full 'cedille-mode-normalize-receive-full-response 'cedille-mode-normalize-receive-response))
  (setq symbol (if full 'normalized 'head-normalized))
  (if (and lang-level (or (string= lang-level "term") (string= lang-level "type")))
      (se-inf-interactive 'cedille-mode-normalize-request-text fn :span span :extra (list lang-level full) :restore t :header "Normalizing")
      (message "Node must be a term or a type")))

(defun cedille-mode-erase-span (span)
  "Erases span"
  (setq lang-level (cdr (assoc 'language-level (se-term-data span))))
  (if (and lang-level (string= lang-level "term"))
      (se-inf-interactive 'cedille-mode-erase-request-text 'cedille-mode-erase-receive-response :span span :restore t :header "Erasing")
      (message "Node must be a term")))


(defun cedille-mode-normalize-request-text(span extra)
  "Gets the text to send to the backend as a request to normalize a span"
  (setq lang-level (car extra))
  (setq full (nth 1 extra))
  (setq s (se-span-start span))
  (setq e (se-span-end span))
  (concat "normalize"
	  sep (format "%s" s)
	  sep (buffer-substring-no-properties s e)
	  sep lang-level
	  sep (file-truename (buffer-file-name))
	  sep (if full "tt" "ff")
	  (cedille-mode-normalize-local-context-param span)))

(defun cedille-mode-erase-request-text(span)
  "Gets the text to send to the backend as a request to normalize a span"
  (setq s (se-span-start span))
  (setq e (se-span-end span))
  (concat "erase"
	  sep (format "%s" s)
	  sep (buffer-substring-no-properties s e)
	  sep (file-truename (buffer-file-name))
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

(defun cedille-mode-normalize-receive-full-response (response span extra)
  "Receives the normalized text response from the backend. Handler for when the user requested a span to be normalized."
  (cedille-mode-normalize-erase-receive-response 'normalized span response))

(defun cedille-mode-normalize-receive-response (response span extra)
  "Receives the head-normalized text response from the backend. Handler for when the user requested a span to be head-normalized."
  (cedille-mode-normalize-erase-receive-response 'head-normalized span response))

(defun cedille-mode-erase-receive-response (response span)
  "Receives the erasure text response from the backend. Handler for when the user requested a span to be erased."
  (cedille-mode-normalize-erase-receive-response 'erased span response))

(defun cedille-mode-normalize-erase-receive-response (symbol span response)
  "Receives the text response from the backend and adds (symbol . response) to span."
  (cedille-mode-normalize-inspect span)
  (add-hook 'se-inf-interactive-response-hook #'cedille-mode-inspect)
  (cons symbol response))

(defun cedille-mode-normalize-inspect (span)
  "Updates the inspect buffer and opens it if it is closed"
  (when (eq span (se-get-span se-mode-selected))
    (display-buffer (cedille-mode-inspect-buffer))))




;;;;;;;;        Prompt Code        ;;;;;;;;

(defun cedille-mode-normalize-prompt (full)
  "Prompts the user to input an expression to normalize"
  (setq input (call-interactively (if full 'cedille-mode-normalize-full-open-prompt 'cedille-mode-normalize-open-prompt)))
  (se-inf-interactive (concat "normalizePrompt" sep input sep (if full "tt" "ff")) 'cedille-mode-normalize-receive-response-prompt :header "Normalizing"))

(defun cedille-mode-normalize-receive-response-prompt(response)
  "Receives the normalize text response (or error text) from the backend. Handler for when the user typed an expression into the prompt."
  (cedille-mode-scratch-display-text (se-inf-undo-escape-string response)))

(defun cedille-mode-normalize-open-prompt (text)
  (interactive "MHead-normalize: ")
  text)

(defun cedille-mode-normalize-full-open-prompt (text)
  (interactive "MNormalize: ")
  text)

(defun cedille-mode-erase-prompt (input)
  (interactive "MErase: ")
  (se-inf-interactive (concat "erasePrompt" sep input) 'cedille-mode-normalize-receive-response-prompt :header "Erasing"))

(provide 'cedille-mode-normalize)
