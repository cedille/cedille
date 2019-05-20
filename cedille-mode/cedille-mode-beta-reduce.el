;;;;; Cedille Beta-Reduce Mode / Beta-Reduction Buffer ;;;;;


;;;;; Faces ;;;;;

(defgroup cedille-highlight-faces-beta-reduction nil
  "Faces used in Cedille's beta-reduction buffer."
  :group 'cedille-highlight)

(defface cedille-checking-face-br
  '((((background light))
     (:overline "dark green"))
    (((background dark))
     (:overline "light green")))
  "The face used when the initial term checks against the current type."
  :group 'cedille-highlight-faces-beta-reduction)


;;;;; Variables ;;;;;

(make-variable-buffer-local
 (defvar cedille-mode-br-range nil
   "The point to jump to and select the next parent span from after a command"))

(make-variable-buffer-local
 (defvar cedille-mode-br-in-buffer nil
   "Whether or not you are in the beta-reduction buffer"))

(make-variable-buffer-local
 (defvar cedille-mode-br-temp-str nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-do-check nil
   "If non-nil, and buffer was opened with `C-i t', messages when the expected type matches the actual type"))

(make-variable-buffer-local
 (defvar cedille-mode-br-path nil
   "A pointer to which beta-reduction buffer instance this is"))

(make-variable-buffer-local
 (defvar cedille-mode-br-column nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-checks nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-local-context nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-parent nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-children nil))


;;;;; Context Buffer ;;;;;

(defmacro cedille-mode-br-show-context (&optional jump-to-window-p)
  "Macro for showing context with `c' or `C' while in `beta-reduce-mode'"
  `(lambda ()
     (interactive)
     (call-interactively
      (make-cedille-mode-buffer (cedille-mode-context-buffer) lambda cedille-context-view-mode nil nil))
     (when ,jump-to-window-p
       (select-window (get-buffer-window (cedille-mode-context-buffer-name))))
     (cedille-mode-update-buffers)))

;;;;; Mode ;;;;;

(defvar cedille-br-keymap
  (progn
    (se-navi-define-key 'cedille-br-mode (kbd "f") #'cedille-mode-select-next)
    (se-navi-define-key 'cedille-br-mode (kbd "F") #'cedille-mode-select-next-alt)
    (se-navi-define-key 'cedille-br-mode (kbd "b") #'cedille-mode-select-previous)
    (se-navi-define-key 'cedille-br-mode (kbd "B") #'cedille-mode-select-previous-alt)
    (se-navi-define-key 'cedille-br-mode (kbd "p") #'cedille-mode-select-parent)
    (se-navi-define-key 'cedille-br-mode (kbd "n") #'cedille-mode-select-first-child)
    (se-navi-define-key 'cedille-br-mode (kbd "e") #'cedille-mode-select-last)
    (se-navi-define-key 'cedille-br-mode (kbd "a") #'cedille-mode-select-first)
    (se-navi-define-key 'cedille-br-mode (kbd "g") #'se-mode-clear-selected)
    (se-navi-define-key 'cedille-br-mode (kbd "H") #'cedille-mode-interactive-highlight)
    (se-navi-define-key 'cedille-br-mode (kbd "q") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "Q") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "M-s") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "C-g") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "j") #'cedille-mode-br-jump)
    (se-navi-define-key 'cedille-br-mode (kbd "c") (cedille-mode-br-show-context))
    (se-navi-define-key 'cedille-br-mode (kbd "C") (cedille-mode-br-show-context t))
    (se-navi-define-key 'cedille-br-mode (kbd "s") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode nil nil))
    (se-navi-define-key 'cedille-br-mode (kbd "S") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode t nil))
    (se-navi-define-key 'cedille-br-mode (kbd "i") (make-cedille-mode-buffer (cedille-mode-inspect-buffer) lambda cedille-mode-inspect nil t))
    (se-navi-define-key 'cedille-br-mode (kbd "I") (make-cedille-mode-buffer (cedille-mode-inspect-buffer) lambda cedille-mode-inspect t t))
    (se-navi-define-key 'cedille-br-mode (kbd "m") (make-cedille-mode-buffer (cedille-mode-meta-vars-buffer) lambda cedille-meta-vars-mode nil t))
    (se-navi-define-key 'cedille-br-mode (kbd "M") (make-cedille-mode-buffer (cedille-mode-meta-vars-buffer) lambda cedille-meta-vars-mode t t))
    (se-navi-define-key 'cedille-br-mode (kbd "#") #'cedille-mode-highlight-occurrences)
    (se-navi-define-key 'cedille-br-mode (kbd "K") #'cedille-mode-restart-backend)
    (se-navi-define-key 'cedille-br-mode (kbd "h") (make-cedille-mode-info-display-page "beta-reduce mode"))
    (se-navi-define-key 'cedille-br-mode (kbd "$") (make-cedille-mode-customize "cedille"))
    (se-navi-define-key 'cedille-br-mode (kbd "x") #'cedille-mode-scratch-toggle)
    (se-navi-define-key 'cedille-br-mode (kbd "X") (lambda () (interactive) (cedille-mode-scratch-toggle t)))
    (se-navi-define-key 'cedille-br-mode (kbd "M-c") #'cedille-mode-scratch-copy-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "+") (make-cedille-mode-resize-current-window 1))
    (se-navi-define-key 'cedille-br-mode (kbd "-") (make-cedille-mode-resize-current-window -1))
    (se-navi-define-key 'cedille-br-mode (kbd "=") #'cedille-mode-unlock-current-window-size)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i n") #'cedille-mode-br-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i h") #'cedille-mode-br-head-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i u") #'cedille-mode-br-single-reduction)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i =") #'cedille-mode-br-conv)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i r") #'cedille-mode-br-rewrite)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i R") #'cedille-mode-br-rewrite-plus)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i p") #'cedille-mode-br-print-outline)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i a") #'cedille-mode-br-abs)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i f") #'cedille-mode-br-fill-prompt)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i c") #'cedille-mode-br-case)
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
    (add-hook    'se-inf-init-spans-hook  #'cedille-mode-initialize-spans t t)
    (add-hook    'se-inf-pre-parse-hook   #'se-mode-clear-selected        t t)
    (add-hook    'se-inf-post-parse-hook  #'cedille-mode-br-post-parse    t t)
    (remove-hook 'se-inf-pre-parse-hook   #'cedille-mode-clear-buffers      t)
    (remove-hook 'se-inf-pre-parse-hook   #'se-inf-save                     t)
    (remove-hook 'before-change-functions #'se-navigation-mode-quit         t))
  (unless cedille-br-mode
    (message "Quitting cedille-br-mode")))



;;;;; Buffer ;;;;;

(defun cedille-mode-br-buffer-name ()
  "The base name for the beta-reduction buffer"
  "*cedille-beta-reduce*")

(defun cedille-mode-br-buffer ()
  "Creates or gets the beta-reduction buffer"
  (if cedille-mode-br-in-buffer
      (current-buffer)
    (get-buffer-create (cedille-mode-br-buffer-name))))

(defun cedille-mode-br-init-buffer (str &optional span do-check path column)
  "Initializes the beta-reduction buffer, after the process finishes"
  (se-inf-interactive
   "status ping"
   `(lambda (r e)
      (cedille-mode-br-init-buffer-post ,str ,span ,do-check ,path ,column))
   nil))

(defun cedille-mode-br-init-buffer-post (str span do-check path column)
  "Initializes the beta-reduction buffer"
  (let* ((span (when span (se-get-span span)))
         (parent (or cedille-mode-parent-buffer (current-buffer)))
         (context (when span (cedille-mode-span-context span)))
         (qed (when span (cedille-mode-br-get-qed span)))
         (buffer (generate-new-buffer (cedille-mode-br-buffer-name))))
    (with-current-buffer buffer
      (display-buffer-in-side-window buffer (list (cons 'side 'bottom)))
      (select-window (get-buffer-window))
      (let ((buffer-read-only nil)) (insert str))
      (setq buffer-read-only t)
      (se-navigation-mode)
      (cedille-br-mode)
      (se-inf-start (get-buffer-process "*cedille-mode*"))
      (setq cedille-mode-parent-buffer parent
	    se-inf-response-finished t
	    cedille-mode-do-update-buffers t
	    cedille-mode-br-in-buffer t
            cedille-mode-br-do-check (and qed do-check
                                          (cons (se-term-start span) (se-term-end span)))
	    cedille-mode-global-context context
            cedille-mode-br-local-context context
            cedille-mode-br-column column
            cedille-mode-br-path path
	    window-size-fixed nil)
      (se-inf-interactive
       (cedille-mode-concat-sep
        "interactive"
        "br2"
        str
        (or qed "●")
        (number-to-string (if span (1- (se-span-start span)) (point-max)))
        (if context (cedille-mode-normalize-local-context-to-string (copy-tree context)) ""))
       (cedille-mode-response-macro #'cedille-mode-br-response)
       nil))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-br-spawn-buffer (str path)
  "Spawns a child beta-reduction buffer from another one"
  (let* ((parent cedille-mode-parent-buffer)
         (br-parent (current-buffer))
         (buffer (generate-new-buffer (cedille-mode-br-buffer-name)))
         (context (copy-tree cedille-mode-global-context))
         (column cedille-mode-br-column))
    (with-current-buffer br-parent
      (add-to-list 'cedille-mode-br-children buffer))
    (with-current-buffer parent
      (with-selected-window (get-buffer-window)
        (cedille-mode-get-create-window buffer)))
    (with-current-buffer buffer
      (select-window (get-buffer-window))
      (let ((buffer-read-only nil)) (insert str))
      (se-navigation-mode)
      (cedille-br-mode)
      (se-inf-start (get-buffer-process "*cedille-mode*"))
      (setq cedille-mode-parent-buffer parent
            se-inf-response-finished t
	    cedille-mode-do-update-buffers t
	    cedille-mode-br-in-buffer t
            cedille-mode-br-parent br-parent
	    cedille-mode-global-context context
            cedille-mode-br-local-context context
            cedille-mode-br-column column
            cedille-mode-br-path path
	    window-size-fixed nil)
      (cedille-mode-br-response str t))
    (cedille-mode-rebalance-windows)
    buffer))


;;;;; Helpers ;;;;;

(defun cedille-mode-br-response (response update-context &optional span)
  (when span (setq cedille-mode-br-range (cons (se-term-start span) (+ (se-term-end span) (length response) (- (point-max))))))
  (setq cedille-mode-br-temp-str response)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (se-inf-interactive (cedille-mode-concat-sep "br" (cedille-mode-br-path) "parse") #'cedille-mode-br-process-response (cons update-context span))
  nil)

(defun cedille-mode-br-process-response (response extra)
  (when response
    (se-inf-process-response response (current-buffer))
    (unless (cdr extra)
      (setq se-mode-not-selected (list (se-get-span (se-mode-parse-tree)))))
    (cedille-mode-matching-nodes-init)
    (when (car extra) (cedille-mode-br-update-context)))
  nil)

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
    (when cedille-mode-br-range
      (goto-char (car cedille-mode-br-range))
      (push-mark (cdr cedille-mode-br-range) t t)
      (se-mode-set-spans)
      (cedille-mode-select-parent 1))
    (cedille-mode-br-fill "" t))
  (setq cedille-mode-br-range nil))  

(defun cedille-mode-br-sync ()
  "Syncs with the backend"
  (interactive)
  (se-inf-interactive
   (cedille-mode-concat-sep "br" (cedille-mode-br-path) "get")
   (cedille-mode-response-macro #'cedille-mode-br-response)
   t))

(defun cedille-mode-br-update-context (&optional fn)
  "Updates the context, querying the backend"
  (interactive)
  (se-inf-interactive
   (cedille-mode-concat-sep "br" (cedille-mode-br-path) "context")
   (cedille-mode-response-macro
    (lambda (response extra)
      (cedille-mode-br-add-to-context response)
      (cedille-mode-update-buffers)
      (when extra (funcall extra))))
   fn))

(defun cedille-mode-br-path ()
  "Concatenates all the strings in `cedille-mode-br-path'"
  (se-foldr cedille-mode-br-path "" (lambda (p x) (concat x " " p))))

(defun cedille-mode-br-add-to-context (decls)
  "Adds a symbol and its type/kind to the global context"
  (setq cedille-mode-global-context
        (let ((cedille-mode-global-context cedille-mode-br-local-context))
          (cedille-mode-get-context
           (list
            (se-new-span "dummy" 0 0
                         (mapcar
                          (lambda (decl)
                            (if (string= (intern "binder") (car decl))
                                (cons (car decl)
                                      (if (consp (cdr decl))
                                          (cedille-mode-parse-binder
                                           (cedille-mode-apply-tags
                                            (cadr decl) (caddr decl)))
                                        (cdr decl)))
                              decl))
                          decls)))))))

;;;;; Undo/Redo ;;;;;

(defconst cedille-mode-br-undo-response
  (cedille-mode-response-macro
   (lambda (response &rest args)
     (message response)
     (cedille-mode-br-sync)))
  "The function that handles the backend's response after the user undoes or redoes")

(defun cedille-mode-br-undo ()
  "Undoes the previous buffer change"
  (interactive)
  (se-inf-interactive
   (cedille-mode-concat-sep "br" (cedille-mode-br-path) "undo")
   cedille-mode-br-undo-response
   nil))

(defun cedille-mode-br-redo ()
  "Redoes the previous undo"
  (interactive)
  (se-inf-interactive
   (cedille-mode-concat-sep "br" (cedille-mode-br-path) "redo")
   cedille-mode-br-undo-response
   nil))


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
          (cedille-mode-br-init-buffer type node t nil (format-mode-line "%c"))
        (message "Span must have an expected type or a type"))))
  nil)


(defun cedille-mode-br-prompt (str)
  "Starts the beta-reduction buffer with STR and local context"
  (cedille-mode-br-init-buffer str (se-mode-selected)))

(defun cedille-mode-br-kill-buffer (&optional on-kill)
  "Kills the current buffer, calling optional ON-KILL afterwards"
  (interactive)
  (if (null cedille-mode-br-parent)
      (let ((buffer (current-buffer))
            (window (get-buffer-window)))
        ;(loop for child in cedille-mode-br-children
        ;      do (with-current-buffer child (cedille-mode-br-kill-buffer)))
        (se-inf-interactive
         (cedille-mode-concat-sep "br" (cedille-mode-br-path) "quit")
         `(lambda (response extra)
            (kill-buffer (cadr extra))
            (when (car extra) (funcall (car extra))))
         (cons on-kill (cons buffer window))))
    (let ((buffer (if (buffer-live-p cedille-mode-br-parent)
                      cedille-mode-br-parent
                    cedille-mode-parent-buffer))
          (window (get-buffer-window)))
      (kill-buffer)
      (delete-window window)
      (select-window (get-buffer-window buffer))))
  nil)

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


;;;;; Jumping ;;;;;

(defun cedille-mode-br-jump ()
  "Jumps to the location of the selected symbol node"
  (interactive)
  (let ((sel se-mode-selected))
    (select-window (get-buffer-window cedille-mode-parent-buffer))
    (let ((se-mode-selected sel))
      (cedille-mode-jump))))


;;;;; Normalizing ;;;;;

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
            "br"
            (cedille-mode-br-path) 
            "normalize"
            (number-to-string (1- (se-span-start span)))
            (number-to-string (1- (se-span-end span)))
            (cedille-mode-norm-method-case (or norm-method 'normalized) "all" "head" "once")
            (cedille-mode-normalize-local-context-to-string (copy-tree (let (cedille-mode-global-context) (cedille-mode-span-context span)))))
	   (cedille-mode-response-macro #'cedille-mode-br-response)
	   nil
           span))))))

(defun cedille-mode-br-head-normalize ()
  "Replace the selected span with its head-normalized value"
  (interactive)
  (cedille-mode-br-normalize 'head-normalized))

(defun cedille-mode-br-single-reduction ()
  "Replace the selected span after performing a single reduction on it"
  (interactive)
  (cedille-mode-br-normalize 'single-reduction))


;;;;; Conversion ;;;;;

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
                   "br"
                   (cedille-mode-br-path)
                   "conv"
		   ll
		   (number-to-string (1- (se-span-start span)))
                   (number-to-string (1- (se-span-end span)))
		   input
		   (let (cedille-mode-global-context) (cedille-mode-normalize-local-context-param span)))))
	  (se-inf-interactive-with-span
	   q
	   (cedille-mode-response-macro #'cedille-mode-br-response)
	   nil
           span))))))


;;;;; Rewriting ;;;;;

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
                 "br"
                 (cedille-mode-br-path)
                 "rewrite"
                 (number-to-string (1- (se-span-start span)))
                 (number-to-string (1- (se-span-end span)))
                 input
                 (if head "tt" "ff")
                 (let (cedille-mode-global-context) (cedille-mode-normalize-local-context-param span)))))
        (se-inf-interactive-with-span
         q
         (cedille-mode-response-macro #'cedille-mode-br-response)
         nil
         span)))))

(defun cedille-mode-br-rewrite-plus ()
  "Rewrite while beta-reducing the selected span, using an input expression"
  (interactive)
  (cedille-mode-br-rewrite t))


;;;;; Printing ;;;;;

(defun cedille-mode-br-print-outline ()
  "Prints an outline of every normalization, conversion, and rewrite applied in the beta-reduction buffer to help reconstruct a proof"
  (interactive)
  (se-inf-interactive
   (cedille-mode-concat-sep "br" (cedille-mode-br-path) "print" cedille-mode-br-column)
   (cedille-mode-response-macro
    (lambda (response extra)
      (if extra
          (lexical-let* ((s (car extra))
                         (e (cdr extra)))
            (cedille-mode-br-kill-buffer
             `(lambda ()
                (with-cedille-buffer t
                  (let ((buffer-read-only nil))
                    (cedille-mode-quit)
                    (delete-region ,s ,e)
                    (goto-char ,s)
                    (deactivate-mark)
                    (insert "(" ,response ")")
                    (cedille-start-navigation))))))
        (with-cedille-buffer nil
          (cedille-mode-scratch-insert-text response)))))
   cedille-mode-br-do-check))


;;;;; Abstracting ;;;;;

(defun cedille-mode-br-abs ()
  (interactive)
  (let* ((top (se-get-span (se-mode-parse-tree)))
         (data (when top (se-term-data top)))
         (bs (when data (cdr (assoc 'binder data))))
         (sym (when bs (cdr (assoc 'symbol bs))))
         (fn
          (if sym
              `(lambda (x)
                 (interactive ,(format "MName (default %s): " sym))
                 (if (zerop (length x)) ,sym x))
            (lambda (x)
              (interactive "MName: ")
              x)))
         (x (call-interactively fn)))
    (se-inf-interactive-with-span ; used to be without span
     (cedille-mode-concat-sep "br" (cedille-mode-br-path) "bind" x)
     (cedille-mode-response-macro #'cedille-mode-br-response) ;
;     (cedille-mode-response-macro
;      (lambda (response top)
;        (cedille-mode-br-add-to-context (list (cons 'binder (car response))))
;        (cedille-mode-br-response (cadr response) nil top)))
     t
     top)))


;;;;; Case Splitting ;;;;;

(defun cedille-mode-br-case (scrutinee)
  "Case split over a scrutinee (currently, must be a datatype)"
  (interactive "MScrutinee: ")
  (let ((rec (call-interactively
              (lambda (x)
                (interactive "MRecursive name (optional): ")
                x))))
    (se-inf-interactive
     (cedille-mode-concat-sep "br" (cedille-mode-br-path) "case" scrutinee rec)
     (cedille-mode-response-macro #'cedille-mode-br-case-response)
;     (cedille-mode-response-macro
;      (lambda (response extra)
;        (cedille-mode-br-add-to-context (mapcar (lambda (tv) (cons (car tv) (cadr tv))) (car response)))
;        (cedille-mode-br-case-response (cadr response))
;        ))
     nil)))

(defun cedille-mode-br-case-response (response &optional extra)
  "Response function for `cedille-mode-br-case'"
  (lexical-let ((cases response))
    (cedille-mode-br-update-context
     (lambda (&rest args)
        (let ((n (length cases)))
          (loop for (key . val) in (reverse cases)
                do (progn
                     (decf n)
                     (cedille-mode-br-spawn-buffer
                      val (cons (number-to-string n) cedille-mode-br-path)))))))))


;;;;; Checking ;;;;;

(defun cedille-mode-br-fill-prompt (qed)
  "Check some term/type against the expression, which must be either a type or a kind"
  (interactive "MFill with: ")
  (cedille-mode-br-fill qed))

(defun cedille-mode-br-fill (qed &optional suppress-err)
  "If `cedille-mode-br-column' is non-nil, check if the expected type matches the actual type"
  (cedille-mode-br-clear-check)
  (when cedille-mode-br-column
    (se-inf-interactive
     (if (zerop (length qed))
         (cedille-mode-concat-sep "br" (cedille-mode-br-path) "check")
       (cedille-mode-concat-sep "br" (cedille-mode-br-path) "check" qed))
     (if suppress-err
         (cedille-mode-response-macro-suppress-err #'cedille-mode-br-fill-response)
       (cedille-mode-response-macro #'cedille-mode-br-fill-response))
     suppress-err)))

(defun cedille-mode-br-fill-response (response suppress-msg &optional span)
  "Handles response from backend, after a query as to whether a term checks against the current expression"
  (cedille-mode-br-does-check)
  (when cedille-mode-br-parent
    (with-current-buffer cedille-mode-br-parent
      (when (funcall
             `(lambda ()
                (and ,@(mapcar
                        (lambda (child)
                          (if (buffer-live-p child)
                              (with-current-buffer child
                                cedille-mode-br-checks)
                            t))
                        cedille-mode-br-children))))
        (cedille-mode-br-does-check))))
  (unless suppress-msg
    (message response)))

(defun cedille-mode-br-clear-check ()
  "Clears `cedille-checking-face-br' and resets `cedille-mode-br-checks' to nil"
  (setq cedille-mode-br-checks nil)
  (with-silent-modifications
    (put-text-property (point-min) (point-max) 'face nil)))

(defun cedille-mode-br-does-check ()
  "Applies `cedille-checking-face-br' and sets `cedille-mode-br-checks' to t"
  (setq cedille-mode-br-checks t)
  (with-silent-modifications
    (put-text-property (point-min) (point-max) 'face 'cedille-checking-face-br)))

;;;;; End ;;;;;

(provide 'cedille-mode-beta-reduce)
