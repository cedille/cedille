


;;;;;;;; Variables ;;;;;;;;

(make-variable-buffer-local
 (defvar cedille-mode-br-point nil
   "The point to jump to and select the next parent span from after a command"))

(make-variable-buffer-local
 (defvar cedille-mode-br-in-buffer nil
   "Whether or not you are in the beta-reduction buffer"))

(make-variable-buffer-local
 (defvar cedille-mode-br-temp-str nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-print-in-buffer nil
   "A boolean governing whether or not to actually insert the printed proof into the file buffer, or the scratch buffer"))


;;;;;;;; Mode code ;;;;;;;;

(defvar cedille-br-keymap
  (progn
    (funcall 'cedille-modify-keymap 'cedille-br-mode)
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
    (se-navi-define-key 'cedille-br-mode (kbd "C-i B") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i t") #'se-navi-nothing)
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
    (setq se-navi-current-keymap (se-navi-get-keymap 'cedille-br-mode))
    (make-local-variable 'minor-mode-overriding-map-alist)
    (push (cons 'se-navigation-mode se-navi-current-keymap) minor-mode-overriding-map-alist)
    (add-hook    'se-inf-init-spans-hook  #'cedille-mode-initialize-spans  t   t)
    (remove-hook 'se-inf-pre-parse-hook   #'cedille-mode-clear-buffers         t)
    (add-hook    'se-inf-pre-parse-hook   #'se-mode-clear-selected         t   t)
    (add-hook    'se-inf-post-parse-hook  #'cedille-mode-br-post-parse     t   t)
    (remove-hook 'se-inf-pre-parse-hook   #'se-inf-save                        t)
    (remove-hook 'before-change-functions #'se-navigation-mode-quit            t))
  (unless cedille-br-mode
    (message "Quitting cedille-br-mode")))


;;;;;;;; Buffer/file code ;;;;;;;;

(defun cedille-mode-br-init-buffer (str &optional span)
  "Initializes the beta-reduction buffer, after the process finishes"
  (se-inf-interactive "status ping" `(lambda (r e) (cedille-mode-br-init-buffer-post ,str ,span)) nil))

(defun cedille-mode-br-init-buffer-post (str span)
  "Initializes the beta-reduction buffer"
  (let* ((span (when span (se-get-span span)))
         (parent (or cedille-mode-parent-buffer (current-buffer)))
         (context (when span (cedille-mode-span-context span)))
         (qed (when span (cedille-mode-br-get-qed span)))
         (buffer (generate-new-buffer (cedille-mode-br-buffer-name))))
    (with-current-buffer buffer
      (cedille-mode-get-create-window buffer)
      (display-buffer buffer)
      (select-window (get-buffer-window))
      (let ((buffer-read-only nil)) (insert str))
      (setq buffer-read-only t)
      (se-navigation-mode)
      (cedille-br-mode)
      (se-inf-start (get-buffer-process "*cedille-mode*"))
      (setq cedille-mode-parent-buffer parent
            se-mode-not-selected se-mode-parse-tree
	    se-inf-response-finished t
	    cedille-mode-do-update-buffers nil
	    cedille-mode-br-in-buffer t
            cedille-mode-br-print-in-buffer (when span (cons (se-span-start span) (se-span-end span)))
	    cedille-mode-global-context nil
	    window-size-fixed nil)
      (se-inf-interactive
       (cedille-mode-concat-sep
        "interactive"
        "br2"
        str
        (or qed "●")
        (number-to-string (if span (1- (se-span-start span)) (point-max)))
        (if context (cedille-mode-normalize-local-context-to-string context) ""))
       (cedille-mode-response-macro #'cedille-mode-br-response)
       buffer))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-br-response (response buffer &optional span)
  (with-current-buffer buffer
    (when span (setq cedille-mode-br-point (se-term-start span)))
    (setq cedille-mode-br-temp-str response)
    (run-hooks 'se-inf-pre-parse-hook)
    (setq se-inf-response-finished nil)
    (se-inf-interactive "parse" #'cedille-mode-br-process-response buffer))
  nil)

(defconst cedille-mode-br-undo-response
  (cedille-mode-response-macro
   (lambda (response buffer &rest args)
     (message response)
     (with-current-buffer buffer
       (cedille-mode-br-sync))))
  "The function that handles the backend's response after the user undoes or redoes")

(defun cedille-mode-br-undo ()
  "Undoes the previous buffer change"
  (interactive)
  (se-inf-interactive
   "undo"
   cedille-mode-br-undo-response
   (current-buffer)))

(defun cedille-mode-br-redo ()
  "Redoes the previous undo"
  (interactive)
  (se-inf-interactive
   "redo"
   cedille-mode-br-undo-response
   (current-buffer)))

(defun cedille-mode-br-sync ()
  "Syncs with the backend"
  (interactive)
  (se-inf-interactive
   "get"
   (cedille-mode-response-macro #'cedille-mode-br-response)
   (current-buffer)))

(defun cedille-mode-br-process-response (response buffer)
  (when response
    (se-inf-process-response response buffer)
    (cedille-mode-matching-nodes-init)
    nil))

(defun cedille-mode-br-buffer-name ()
  (concat "*cedille-beta-reduce*"))

(defun cedille-mode-br-buffer ()
  "Creates or gets the beta-reduction buffer"
  (if cedille-mode-br-in-buffer
      (current-buffer)
    (get-buffer-create (cedille-mode-br-buffer-name))))

;;;;;;;; Starting code ;;;;;;;;

(defun cedille-mode-br ()
  "Opens the beta-reduction buffer with local context, using a prompted expression"
  (interactive)
  (cedille-mode-br-init-buffer (call-interactively (lambda (input) (interactive "MBeta-reduce: ") input)) (se-mode-selected))
  nil)

(defun cedille-mode-br-node ()
  "Opens the beta-reduction buffer with the selected node"
  (interactive)
  (let ((node (se-mode-selected)))
    (if (not node)
	(message "Error: must select a node")
      (let* ((text (cedille-mode-br-get-qed-h node)))
	(cedille-mode-br-init-buffer text node))))
  nil)

(defun cedille-mode-br-type ()
  "Opens the beta-reduction buffer wit the selected node's expected type (or type if there is no expected type)"
  (interactive)
  (if (not (se-mode-selected))
      (message "Error: must select a node")
    (let* ((node (se-mode-selected))
           (type (or (cdr (assoc 'expected-type (se-term-data node)))
                     (cdr (assoc 'type (se-term-data node))))))
      (if type
          (cedille-mode-br-init-buffer type node)
        (message "Span must have an expected type or a type"))))
  nil)


(defun cedille-mode-br-prompt (str)
  "Starts the beta-reduction buffer with STR and local context"
  (cedille-mode-br-init-buffer str (se-mode-selected)))

(defun cedille-mode-br-kill-buffer ()
  "Kills the current buffer"
  (interactive)
  (let ((buffer (current-buffer))
	(window (get-buffer-window)))
    (se-inf-interactive "quit" `(lambda (&rest args) (kill-buffer ,buffer) (delete-window ,window)) nil)))

(defun cedille-mode-br-get-qed-h (node)
  (let* ((start (se-term-start node))
         (end (min (1+ (buffer-size)) (se-term-end node))))
    (buffer-substring start end)))
  
(defun cedille-mode-br-get-qed (node)
  "Returns the buffer's text from the start to the end of NODE, if it has an error"
  (when (and node
             (cedille-span-has-error-data (se-term-data node))
             (cedille-mode-normalize-get-ll node)
             (string= "term" (cedille-mode-normalize-get-ll node)))
    (cedille-mode-br-get-qed-h node)))


;;;;;;;; Normalizing code ;;;;;;;;

(defun cedille-mode-br-normalize (&optional norm-method)
  "Replace the selected span with its normalized value"
  (interactive)
  (let ((span (se-get-span (se-mode-selected))))
    (if (null span)
	(message "Error: must select a node")
      (let* ((ll (cdr (assoc 'language-level (se-span-data span)))))
	(if (not (and ll (or (string= ll "term") (string= ll "type") (string= ll "kind"))))
	    (message "Node must be a term, type, or kind")
	  (se-inf-interactive-with-span
	   (cedille-mode-concat-sep
            "normalize"
            (number-to-string (1- (se-span-start span)))
            (number-to-string (1- (se-span-end span)))
            (cedille-mode-norm-method-case (or norm-method 'normalized) "all" "head" "once")
            (cedille-mode-normalize-local-context-to-string (copy-tree (cedille-mode-span-context span))))
	   (cedille-mode-response-macro #'cedille-mode-br-response)
	   (current-buffer)
           span))))))

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
	(let* ((input (call-interactively (lambda (input) (interactive "MConvert to: ") input)))
	       (q (cedille-mode-concat-sep
                   "conv"
		   ll
		   (number-to-string (1- (se-span-start span)))
                   (number-to-string (1- (se-span-end span)))
		   input
		   (cedille-mode-normalize-local-context-param span))))
	  (se-inf-interactive-with-span
	   q
	   (cedille-mode-response-macro #'cedille-mode-br-response)
	   (current-buffer)
           span))))))

(defun cedille-mode-br-rewrite (&optional head)
  "Rewrite the selected span, using an input expression"
  (interactive)
  (let ((span (se-get-span (se-mode-selected))))
    (if (null span)
        (message "Error: must select a node")
      (let* ((input (call-interactively
                     `(lambda (input)
                        (interactive ,(if head "MRewrite(+) using: " "MRewrite using: "))
                        input)))
             (q (cedille-mode-concat-sep
                 "rewrite"
                 (number-to-string (1- (se-span-start span)))
                 (number-to-string (1- (se-span-end span)))
                 input
                 (if head "tt" "ff")
                 (cedille-mode-normalize-local-context-param span))))
        (se-inf-interactive-with-span
         q
         (cedille-mode-response-macro #'cedille-mode-br-response)
         (current-buffer)
         span)))))

(defun cedille-mode-br-rewrite-plus ()
  "Rewrite while beta-reducing the selected span, using an input expression"
  (interactive)
  (cedille-mode-br-rewrite t))

(defun cedille-mode-br-post-parse (&optional json)
  "Called after the file was parsed, error or no."
  (if (se-inf-get-error json)
      (progn
        (message (se-inf-get-error json))
        (setq cedille-mode-br-temp-str nil))
    (let ((buffer-read-only nil))
      (erase-buffer)
      (insert cedille-mode-br-temp-str)
      (goto-char 1)
      (deactivate-mark)
      (fit-window-to-buffer))
    (when cedille-mode-br-point
      (se-mode-set-spans)
      (cedille-mode-select-parent 1))))

(defun cedille-mode-br-print-outline ()
  "Prints an outline of every normalization, conversion, and rewrite applied in the beta-reduction buffer to help reconstruct a proof"
  (interactive)
  (se-inf-interactive
   "print"
   (cedille-mode-response-macro
    (lambda (response extra)
      (let ((s (when (car extra) (caar extra)))
            (e (when (car extra) (cdar extra)))
            (cbuffer (cadr extra))
            (fbuffer (cddr extra)))
;        (with-current-buffer cbuffer
;          (cedille-mode-br-kill-buffer))
        (with-current-buffer fbuffer
          (select-window (get-buffer-window))
;          (if (car extra)
;              (let ((buffer-read-only nil))
;                (delete-region s e)
;                (goto-char s)
;                (deactivate-mark)
;                (insert response)
;                (cedille-start-navigation))
            (cedille-mode-scratch-insert-text response)))));)
   (cons cedille-mode-br-print-in-buffer (cons (current-buffer) cedille-mode-parent-buffer))))


(provide 'cedille-mode-beta-reduce2)
