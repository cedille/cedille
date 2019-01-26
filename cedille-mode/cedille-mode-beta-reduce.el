

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
   "A string that represents the most recent operation applied in the buffer, for use in `cedille-mode-br-print-outline'"))

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

(make-variable-buffer-local
 (defvar cedille-mode-br-checking nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-qed nil
   "(original span . original span text"))


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
    (se-navi-define-key 'cedille-br-mode (kbd "m") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "M") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "h") (make-cedille-mode-info-display-page "beta-reduce mode"))
    (se-navi-define-key 'cedille-br-mode (kbd "C-i e") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i b") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i n") #'cedille-mode-br-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i h") #'cedille-mode-br-head-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i u") #'cedille-mode-br-single-reduction)
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
    (setq-local se-inf-progress-prefix "inhabited: ")
    (setq-local se-inf-progress-fn 'cedille-mode-br-progress-fn)
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

(defun cedille-mode-br-progress-fn (response &optional oc buffer span)
  "Beta-Reduction buffer progress function for telling you when the type is inhabited"
  (message response)
  cedille-mode-progress-msg)


;;;;;;;; Buffer/file code ;;;;;;;;

(defun cedille-mode-br-init-buffer (str &optional context checking qed)
  "Initializes the beta-reduction buffer"
  (let ((parent cedille-mode-parent-buffer)
        (original-filename (buffer-file-name))
        (len (buffer-size))
	(buffer (generate-new-buffer (cedille-mode-br-buffer-name))))
    (with-current-buffer buffer
      (cedille-mode-get-create-window buffer)
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
            cedille-mode-br-checking checking
            cedille-mode-br-qed (or qed (cons nil "●"))
	    cedille-mode-global-context context
	    buffer-read-only nil
	    window-size-fixed nil)
      (cedille-mode-br-erase str))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-br-erase (s)
  "Erases the text before parsing"
  (se-inf-interactive
   (cedille-mode-concat-sep
    "interactive"
    "erasePrompt"
    s
    (cedille-mode-normalize-local-context-to-string cedille-mode-global-context))
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
  (when response
    (se-inf-process-response response buffer)
    (cedille-mode-matching-nodes-init)))

(defun cedille-mode-br-parse ()
  (interactive)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (se-inf-interactive
   (cedille-mode-concat-sep
    "interactive"
    "br"
    cedille-mode-br-temp-str
    (cdr cedille-mode-br-qed)
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

;;;;;;;; Starting code ;;;;;;;;

(defun cedille-mode-br ()
  "Opens the beta-reduction buffer with local context, using a prompted expression"
  (interactive)
  (let ((cedille-mode-br-original-filename (buffer-file-name))
	(node (se-mode-selected)))
    (if node
	(cedille-mode-br-start-prompt (cedille-mode-get-context se-mode-not-selected) (cedille-mode-br-is-checking))
      (cedille-mode-br-start-prompt nil t)))
  nil)

(defun cedille-mode-br-node ()
  "Opens the beta-reduction buffer with the selected node"
  (interactive)
  (let ((cedille-mode-br-original-filename (buffer-file-name))
	(node (se-mode-selected)))
    (if (not node)
	(message "Error: must select a node")
      (let* ((text (cedille-mode-br-get-qed-h node)))
	(cedille-mode-br-init-buffer (cdr text) (cedille-mode-get-context se-mode-not-selected) (cedille-mode-br-is-checking)))))
  nil)

(defun cedille-mode-br-type ()
  "Opens the beta-reduction buffer wit the selected node's expected type (or type if there is no expected type)"
  (interactive)
  (if (not (se-mode-selected))
      (message "Error: must select a node")
    (let* ((cedille-mode-br-original-filename (buffer-file-name))
           (span (se-mode-selected))
           (type (or (cdr (assoc 'expected-type (se-term-data span)))
                     (cdr (assoc 'type (se-term-data span))))))
      (if type
          (cedille-mode-br-init-buffer type (cedille-mode-get-context se-mode-not-selected) (cedille-mode-br-is-checking) (cedille-mode-br-get-qed span))
        (message "Span must have an expected type or a type"))))
  nil)

(defun cedille-mode-br-start-prompt (&optional context checking)
  "Starts beta-reduction buffer with the prompted input INPUT"
  (cedille-mode-br-init-buffer (call-interactively (lambda (input) (interactive "MBeta-reduce: ") input)) context checking))

(defun cedille-mode-br-prompt (str)
  "Starts the beta-reduction buffer with STR and local context"
  (let ((cedille-mode-br-original-filename (buffer-file-name)))
    (cedille-mode-br-init-buffer str (cedille-mode-get-context se-mode-not-selected) (cedille-mode-br-is-checking))))

(defun cedille-mode-br-kill-buffer ()
  "Kills the current buffer"
  (interactive)
  (let ((buffer (current-buffer))
	(window (get-buffer-window)))
    (kill-buffer buffer)
    (delete-window window)))

(defun cedille-mode-br-is-checking ()
  "Returns if the current span is checking"
  (when (se-mode-selected)
    (let* ((data (se-term-data (se-mode-selected)))
           (cm (cdr (assoc 'checking-mode data)))
           (et (cdr (assoc 'expected-type data))))
    (if cm (string= "checking" cm) et))))

(defun cedille-mode-br-get-qed-h (node)
  (let* ((start (se-term-start node))
         (end (min (1+ (buffer-size)) (se-term-end node))))
    (cons (se-get-span node) (buffer-substring start end))))

(defun cedille-mode-br-get-qed (node)
  "Returns the buffer's text from the start to the end of NODE, if it has an error"
  (when (and node (cedille-span-has-error-data (se-term-data node)))
    (cedille-mode-br-get-qed-h node)))


;;;;;;;; Normalizing code ;;;;;;;;

(defun cedille-mode-br-normalize (&optional norm-method)
  "Replace the selected span with its normalized value"
  (interactive)
  (let ((span (se-get-span (se-mode-selected))))
    (if (null span)
	(message "Error: must select a node")
      (let* ((ll (cdr (assoc 'language-level (se-span-data span))))
             (extra (cons (current-buffer) (cons t nil))))
	(if (not (and ll (or (string= ll "term") (string= ll "type") (string= ll "kind"))))
	    (message "Node must be a term, type, or kind")
	  (se-inf-interactive-with-span
	   (cedille-mode-normalize-request-text (or norm-method 'normalized) span cedille-mode-br-length)
	   (cedille-mode-response-macro #'cedille-mode-br-receive-response)
	   extra
           span
	   :header "Normalizing"))))))

(defun cedille-mode-br-head-normalize ()
  "Replace the selected span with its head-normalized value"
  (interactive)
  (cedille-mode-br-normalize 'head-normalized))

(defun cedille-mode-br-single-reduction ()
  "Replace the selected span after performing a single reduction on it"
  (interactive)
  (cedille-mode-br-normalize 'single-reduction))

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
	       (extra (cons (current-buffer) (cons t nil)))
	       (q (cedille-mode-concat-sep
		   "interactive"
                   "conv"
		   ll
		   (buffer-substring (se-span-start span) (se-span-end span))
		   input
		   (cedille-mode-normalize-local-context-param span))))
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
             (op-fn1
              (lambda (response)
                (car (split-string response cedille-mode-sep))))
             (op-fn2
              `(lambda (response new-str)
                (let* ((xT (cdr (split-string response ,cedille-mode-sep)))
                       (x (car xT))
                       (T (cadr xT)))
                  (concat "ρ " (cedille-mode-br-add-parens ,input) " @ " x " . " (format new-str T) " - "))))
             (extra (cons (current-buffer) (cons cedille-mode-br-checking (cons op-fn1 op-fn2))))
             (q (cedille-mode-concat-sep
                 "interactive"
                 "rewrite"
                 (buffer-substring (se-span-start span) (se-span-end span))
                 input
                 (if head "tt" "ff")
                 (cedille-mode-normalize-local-context-param span))))
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
  "Receives the response from the backend after a normalization/conversion/rewrite"
  (with-current-buffer (car extra)
    (cedille-mode-br-push-current)
    (setq cedille-mode-br-redo-stack nil)
    (let* ((op-fns (cddr extra))
           (checking (cadr extra))
           (response2 (if (car op-fns) (funcall (car op-fns) response) response))
           (str-range (cedille-mode-br-add-parens-buffer
                       response2 (se-term-start span) (se-term-end span)))
           (temp-str2 (car (cedille-mode-br-add-parens-buffer "%s" (se-term-start span) (se-term-end span))))
           (temp-str (car str-range))
           (op "")
           (op (if (cdr op-fns) (funcall (cdr op-fns) response temp-str2) op))
           (span-range (cdr str-range)))
      (setq cedille-mode-br-temp-str temp-str
            cedille-mode-br-span-range span-range
            cedille-mode-br-checking checking
            cedille-mode-br-current-op op)
      (cedille-mode-br-parse))))

(defun cedille-mode-br-post-parse (&optional json)
  "Called after the file was parsed, error or no."
  (if (se-inf-get-error json)
      (when cedille-mode-br-undo-stack
        (cedille-mode-br-revert (pop cedille-mode-br-undo-stack)))
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
  "Pushes the current frame to either the undo or the redo stack"
  (let ((frame (br-new-frame se-mode-parse-tree (buffer-string) cedille-mode-br-current-op)))
    (push frame (if is-redo cedille-mode-br-redo-stack cedille-mode-br-undo-stack))))

(defun cedille-mode-br-revert (frame)
  "Reverts the buffer to what it was at FRAME"
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
         (cur-op (or cedille-mode-br-current-op ""))
         (qed (cdr cedille-mode-br-qed))
         (node (car cedille-mode-br-qed)))
    (loop for frame in cedille-mode-br-undo-stack do
          (setq out (concat (or (br-frame-op frame) "") out)))
    (let ((proof (concat out cur-op qed)))
      (with-current-buffer cedille-mode-parent-buffer
        (select-window (get-buffer-window))
        (if (null node)
            (cedille-mode-scratch-insert-text proof)
          (let ((buffer-read-only nil))
            (delete-region (se-span-start node) (se-span-end node))
            (goto-char (se-span-start node))
            (deactivate-mark)
            (insert proof)
            (cedille-start-navigation)))))))



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
