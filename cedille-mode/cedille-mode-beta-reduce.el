

(require 'se)
(require 'se-mode)
(require 'se-navi)
(require 'se-inf)
(require 'se-markup)


;;;;;;;; Structures ;;;;;;;;

(defstruct
    (br-frame
     (:constructor br-new-frame (tree str op)))
  tree str op)


;;;;;;;; Variables ;;;;;;;;

(make-variable-buffer-local
 (defvar cedille-mode-br-undo-stack nil
   "A list of br-frames that keeps track of previous trees and strings in the beta-reduction buffers"))

(make-variable-buffer-local
 (defvar cedille-mode-br-redo-stack nil
   "Like `cedille-mode-br-undo-stack', but for redo"))

(make-variable-buffer-local
 (defvar cedille-mode-br-current-op nil
   "A variable that records if the current 'operation' applied is a head-normalization, a normalization, a conversion, a rewrite, or a rewrite+"))

(make-variable-buffer-local
 (defvar cedille-mode-br-filename nil
   "The file that contains `cedille-mode-br-str'"))

(make-variable-buffer-local
 (defvar cedille-mode-br-in-buffer nil
   "Whether or not you are in the beta-reduction buffer"))

(make-variable-buffer-local
 (defvar cedille-mode-br-temp-str nil
   "A temporary variable to hold the buffer's string (after normalization) until it is sucessfully parsed. Gets discarded upon failure."))

(make-variable-buffer-local
 (defvar cedille-mode-br-span-range nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-length nil))


;;;;;;;; Mode code ;;;;;;;;

(defvar cedille-br-keymap
  (progn
    (cedille-modify-keymap 'cedille-br-mode)
    (se-navi-define-key 'cedille-br-mode (kbd "q") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "M-s") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "C-g") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "i") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "I") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "c") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "r") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "R") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "t") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "t") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "s") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "S") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "h") (make-cedille-mode-info-display-page "beta-reduce mode"))
    (se-navi-define-key 'cedille-br-mode (kbd "C-i e") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i b") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i n") #'cedille-mode-br-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i h") #'cedille-mode-br-head-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i =") #'cedille-mode-br-conv)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i r") #'cedille-mode-br-rewrite)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i R") #'cedille-mode-br-rewrite-plus)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i p") #'cedille-mode-br-print-outline)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i ,") #'cedille-mode-br-undo)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i .") #'cedille-mode-br-redo)
    (se-navi-get-keymap 'cedille-br-mode)))

(define-minor-mode cedille-br-mode
  "Minor mode for the beta-reduction buffer"
  nil " Beta-reduce" cedille-br-keymap
  (when cedille-br-mode
    (set-input-method "Cedille")
    (setq-local comment-start "--")
    (setq-local se-inf-get-message-from-filename 'cedille-mode-get-message-from-filename)
    (setq-local se-inf-progress-prefix "progress: ")
    (setq-local se-inf-progress-fn 'cedille-mode-progress-fn)
    (setq se-navi-current-keymap (se-navi-get-keymap 'cedille-br-mode))
    (make-local-variable 'minor-mode-overriding-map-alist)
    (push (cons 'se-navigation-mode se-navi-current-keymap)
	  minor-mode-overriding-map-alist)
    (add-hook    'se-inf-init-spans-hook  #'cedille-mode-initialize-spans  t   t)
    (remove-hook 'se-inf-pre-parse-hook   #'cedille-mode-clear-buffers         t)
    (add-hook    'se-inf-pre-parse-hook   #'se-mode-clear-selected         t   t)
    (add-hook    'se-inf-post-parse-hook  #'cedille-mode-br-post-parse     t   t)
    (remove-hook 'se-inf-pre-parse-hook   #'se-inf-save                        t)
    (remove-hook 'before-change-functions #'se-navigation-mode-quit            t))
  (unless cedille-br-mode
    (message "Quitting cedille-br-mode")))


;;;;;;;; Buffer/file code ;;;;;;;;

(defun cedille-mode-br-init-buffer (str &optional context)
  "Initializes the beta-reduction buffer"
  (let ((parent cedille-mode-parent-buffer)
        (original-filename (buffer-file-name))
	(buffer (generate-new-buffer (cedille-mode-br-buffer-name)))
	(len (buffer-size)))
    (with-current-buffer buffer
      (cedille-mode-get-create-window)
      (display-buffer buffer)
      (setq buffer-read-only t)
      (se-navigation-mode)
      (cedille-br-mode)
      (se-inf-start (get-buffer-process "*cedille-mode*"))
      (setq cedille-mode-parent-buffer parent
            se-mode-not-selected se-mode-parse-tree
	    se-inf-response-finished t
	    cedille-mode-do-update-buffers nil
	    cedille-mode-br-filename original-filename
	    cedille-mode-br-temp-str str
	    cedille-mode-br-in-buffer t
	    cedille-mode-br-length len
	    cedille-mode-global-context context
	    buffer-read-only nil
	    window-size-fixed nil)
      (cedille-mode-br-erase str))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-br-erase (s)
  "Erases the text before parsing"
  (se-inf-interactive
   (concat "interactive§erasePrompt§" s)
   (cedille-mode-response-macro #'cedille-mode-br-erase-response)
   (current-buffer)
   :header "Erasing"))

(defun cedille-mode-br-erase-response (response buffer)
  "Receives the erased response from the backend"
  (with-current-buffer buffer
    (let ((buffer-read-only nil))
      (setq cedille-mode-br-temp-str response)
      (erase-buffer)
      (insert response)
      (select-window (get-buffer-window))
      (goto-char 1)
      (deactivate-mark)
      (cedille-mode-br-parse))))

(defun cedille-mode-br-undo ()
  "Undoes the previous buffer change"
  (interactive)
  (if (null cedille-mode-br-undo-stack)
      (message "No further undo information")
    (cedille-mode-br-push-current t)
    (cedille-mode-br-revert (pop cedille-mode-br-undo-stack))))

(defun cedille-mode-br-redo ()
  "Redoes the previous undo"
  (interactive)
  (if (null cedille-mode-br-redo-stack)
      (message "No further redo information")
    (cedille-mode-br-push-current)
    (cedille-mode-br-revert (pop cedille-mode-br-redo-stack))))

(defun cedille-mode-br-process-response (response buffer)
  (when response (se-inf-process-response response buffer)))

(defun cedille-mode-br-parse ()
  (interactive)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (se-inf-interactive
   (concat "interactive§br"
	   "§" cedille-mode-br-temp-str
	   (cedille-mode-normalize-local-context-to-string cedille-mode-global-context))
   #'cedille-mode-br-process-response
   (current-buffer)
   :header "Parsing"
   :progress-fn se-inf-progress-fn))

(defun cedille-mode-br-buffer-name ()
  (concat "*cedille-beta-reduce*"))

(defun cedille-mode-br-buffer ()
  "Creates or gets the beta-reduction buffer"
  ;(interactive)
  (if cedille-mode-br-in-buffer
      (current-buffer)
    (get-buffer-create (cedille-mode-br-buffer-name))))

(defun cedille-mode-br-is-error (str)
  "Returns t if STR is an error JSON"
  (and (<= 10 (length response)) (string= "{\"error\":\"" (substring str 0 10))))

;;;;;;;; Starting code ;;;;;;;;
(defun cedille-mode-br ()
  "Opens the beta-reduction buffer with local context, using a prompted expression"
  (interactive)
  (let ((cedille-mode-br-original-filename (buffer-file-name))
	(node (se-mode-selected)))
    (if node
	(cedille-mode-br-start-prompt (cedille-mode-get-context se-mode-not-selected))
      (cedille-mode-br-start-prompt)))
  nil)

(defun cedille-mode-br-node ()
  "Opens the beta-reduction buffer with the selected node"
  (interactive)
  (let ((cedille-mode-br-original-filename (buffer-file-name))
	(node (se-mode-selected)))
    (if (not node)
	(message "Error: must select a node")
      (let* ((start (se-term-start node))
	     (end (min (1+ (buffer-size)) (se-term-end node)))
	     (text (buffer-substring start end)))
	(cedille-mode-br-init-buffer text (cedille-mode-get-context se-mode-not-selected))))
  nil))

(defun cedille-mode-br-type ()
  "Opens the beta-reduction buffer wit the selected node's expected type (or type if there is no expected type)"
  (interactive)
  (let* ((span (se-mode-selected))
         (type (or (cdr (assoc 'expected-type (se-term-data span)))
                   (cdr (assoc 'type (se-term-data span))))))
    (if type
        (cedille-mode-br-init-buffer type (cedille-mode-get-context se-mode-not-selected))
      (message "Span must have an expected type or a type")))
  nil)

(defun cedille-mode-br-start-prompt (&optional context)
  "Starts beta-reduction buffer with the prompted input INPUT"
  (cedille-mode-br-init-buffer (call-interactively (lambda (input) (interactive "MBeta-reduce: ") input)) context))

(defun cedille-mode-br-prompt (str)
  "Starts the beta-reduction buffer with STR and local context"
  (cedille-mode-br-init-buffer str (cedille-mode-get-context se-mode-not-selected)))

(defun cedille-mode-br-kill-buffer ()
  "Kills the current buffer"
  (interactive)
  (let ((buffer (current-buffer))
	(window (get-buffer-window)))
    (kill-buffer buffer)
    (delete-window window)))


;;;;;;;; Normalizing code ;;;;;;;;

(defun cedille-mode-br-normalize (&optional head)
  "Replace the selected span with its normalized value"
  (interactive)
  (let ((span (se-get-span (se-mode-selected))))
    (if (null span)
	(message "Error: must select a node")
      (let ((ll (cdr (assoc 'language-level (se-span-data span))))
	    (extra (cons (current-buffer) "ε "))
	    (header (if head "Head-normalizing" "Normalizing")))
	(if (not (and ll (or (string= ll "term") (string= ll "type") (string= ll "kind"))))
	    (message "Node must be a term, type, or kind")
	  (cedille-mode-br-push-current)
	  (setq cedille-mode-br-redo-stack nil)
	  (se-inf-interactive-with-span
	   (cedille-mode-normalize-request-text (if head 'head-normalized 'normalized) span cedille-mode-br-length)
	   (cedille-mode-response-macro #'cedille-mode-br-receive-response)
	   extra
           span
	   :header header))))))

(defun cedille-mode-br-head-normalize ()
  "Replace the selected span with its head-normalized value"
  (interactive)
  (cedille-mode-br-normalize t))

(defun cedille-mode-br-conv ()
  "Replaces the selected span with the prompted expression if they are convertible"
  (interactive)
  (let* ((span (se-get-span (se-mode-selected)))
	 (ll (cdr (assoc 'language-level (se-span-data span)))))
    (if (null span)
	(message "Error: must select a node")
      (if (not (and ll (or (string= ll "term") (string= ll "type") (string= ll "kind"))))
	  (message "Node must be a term, type, or kind")
	(let* ((ask-fn (lambda (input)
			 (interactive "MConvert to: ")
			 input))
	       (input (call-interactively ask-fn))
               (op (concat
                    "χ "
                    (cedille-mode-br-add-parens
                     (car (cedille-mode-br-add-parens-buffer
                           input (se-span-start span) (se-span-end span))))
                    " - "))
	       (extra (cons (current-buffer) op))
	       (q (concat
		   "interactive§conv"
		   "§" ll
		   "§" (buffer-substring (se-span-start span) (se-span-end span))
		   "§" input
		   (cedille-mode-normalize-local-context-param span))))
	  (cedille-mode-br-push-current)
	  (setq cedille-mode-br-redo-stack nil)
	  (se-inf-interactive-with-span
	   q
	   (cedille-mode-response-macro #'cedille-mode-br-receive-response)
	   extra
           span
	   :header "Converting"))))))

(defun cedille-mode-br-rewrite (&optional head)
  "Rewrite the selected span, using an input expression"
  (interactive)
  (let ((span (se-get-span (se-mode-selected))))
    (if (null span)
        (message "Error: must select a node")
      (let* ((ask-fn1 (lambda (input)
                        (interactive "MRewrite using: ")
                        input))
             (ask-fn2 (lambda (input)
                        (interactive "MRewrite(+) using: ")
                        input))
             (input (call-interactively (if head ask-fn2 ask-fn1)))
             (extra (cons (current-buffer) (concat "ρ" (if head "+" "") " " (cedille-mode-br-add-parens input) " - ")))
             (q (concat
                 "interactive§rewrite"
                 "§" (buffer-substring (se-span-start span) (se-span-end span))
                 "§" input
                 "§" (if head "tt" "ff")
                 (cedille-mode-normalize-local-context-param span))))
        (cedille-mode-br-push-current)
        (setq cedille-mode-br-redo-stack nil)
        (se-inf-interactive-with-span
         q
         (cedille-mode-response-macro #'cedille-mode-br-receive-response)
         extra
         span
         :header "Rewriting")))))

(defun cedille-mode-br-rewrite-plus ()
  "Rewrite while beta-reducing the selected span, using an input expression"
  (interactive)
  (cedille-mode-br-rewrite t))

(defun cedille-mode-br-receive-response (response extra span)
  "Receives the normalized response from the backend"
  (with-current-buffer (car extra)
    (let* ((str-range (cedille-mode-br-add-parens-buffer
                       response (se-term-start span) (se-term-end span))))
      (setq cedille-mode-br-temp-str (car str-range)
            cedille-mode-br-span-range (cdr str-range)
            cedille-mode-br-current-op (cdr extra))
      (cedille-mode-br-parse))))

(defun cedille-mode-br-post-parse (&optional json)
  "Called after the file was parsed, error or no."
  (if (se-inf-get-error json)
      (progn
	(when cedille-mode-br-undo-stack
	  (cedille-mode-br-revert (pop cedille-mode-br-undo-stack))))
	;(message "Parse error"))
    (let ((buffer-read-only nil))
      (erase-buffer)
      (insert cedille-mode-br-temp-str)
      (goto-char 1)
      (deactivate-mark)
      (fit-window-to-buffer))
    (when cedille-mode-br-span-range
      (goto-char (car cedille-mode-br-span-range))
      (push-mark (cdr cedille-mode-br-span-range) t t)
      (se-mode-set-spans)
      (cedille-mode-select-parent 1))))

(defun cedille-mode-br-push-current (&optional is-redo)
  "Pushes the current frame to STACK"
  (push (br-new-frame se-mode-parse-tree (buffer-string) cedille-mode-br-current-op)
	(if is-redo cedille-mode-br-redo-stack cedille-mode-br-undo-stack)))

(defun cedille-mode-br-revert (frame)
  "Reverts the buffer to what it was at ITEM"
  (when frame
    (let ((buffer-read-only nil))
      (setq se-mode-parse-tree (br-frame-tree frame)
	    se-mode-selected nil
	    se-mode-not-selected se-mode-parse-tree
            cedille-mode-br-current-op (br-frame-op frame))
      (erase-buffer)
      (insert (br-frame-str frame))
      (goto-char 1)
      (deactivate-mark))))

(defun cedille-mode-br-print-outline ()
  "Prints an outline of every normalization, conversion, and rewrite applied in the beta-reduction buffer to help reconstruct a proof"
  (interactive)
  (let* ((out "")
         (cur-op (or cedille-mode-br-current-op "")))
    (loop for frame in cedille-mode-br-undo-stack do
          (setq out (concat (or (br-frame-op frame) "") out)))
    (with-current-buffer cedille-mode-parent-buffer
      (with-selected-window (get-buffer-window)
        (cedille-mode-scratch-insert-text (concat out cur-op "β"))))))



;;;;;;;; Helper functions ;;;;;;;;

(defun cedille-mode-br-add-parens (str)
  "Adds parentheses to STR unless it already has them"
  (if (or (cedille-mode-str-is-var str) (cedille-mode-br-has-parens-string str)) str (concat "(" str ")")))

(defun cedille-mode-br-add-parens-buffer (str start end)
  "Adds parentheses to STR unless it already has them, then surrounds it with the buffer's text up to START and after END. Returns that cons the new range"
  (let* ((dap (cedille-mode-br-dont-add-parens-buffer str start end))
         (endr (+ start (length str)))
         (range (if dap (cons start endr) (cons (1+ start) (1+ endr))))
         (response (if dap str (concat "(" str ")")))
         (before (buffer-substring 1 start))
         (after (buffer-substring end (1+ (buffer-size)))))
    (cons (concat before response after) range)))

(defun cedille-mode-br-dont-add-parens-buffer (str start end)
  "Returns t if parentheses should NOT be added around STR when replacing the range from START to END in the current buffer"
  (or
   (cedille-mode-br-has-parens-string str)
   (cedille-mode-str-is-var str)
   (and (equal 1 start) (equal end (1+ (buffer-size))))
   (and
    (> start 1)
    (<= end (buffer-size))
    (cedille-mode-br-has-parens-string (buffer-substring (1- start) (1+ end))))))

(defun cedille-mode-is-left-paren (str)
  (or (string= "(" str) (string= "[" str) (string= "{" str)))
(defun cedille-mode-is-right-paren (str)
  (or (string= ")" str) (string= "]" str) (string= "}" str)))

(defun cedille-mode-br-has-parens-string (str)
  "Returns t if parentheses surround STR"
  (let ((size (length str)))
    (and (>= size 2)
	 (cedille-mode-is-left-paren (substring str 0 1))
	 (cedille-mode-is-right-paren (substring str (1- size) size))
	 (cedille-mode-br-has-parens-string-h (substring str 1 (1- size)) 0))))

(defun cedille-mode-br-has-parens-string-h (str parens)
  "Helper for `cedille-mode-br-has-parens-string'"
  (when (>= parens 0)
    (if (equal 0 (length str))
	(equal 0 parens)
      (let ((h (substring str 0 1)))
	(cedille-mode-br-has-parens-string-h
	 (substring str 1)
	 (+ parens (if (cedille-mode-is-left-paren h) 1 (if (cedille-mode-is-right-paren h) -1 0))))))))

(provide 'cedille-mode-beta-reduce)
