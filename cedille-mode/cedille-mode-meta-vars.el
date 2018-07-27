

(defstruct meta-var kind sol file start-intro end-intro start-sol end-sol)

(defvar cedille-mode-meta-vars-list nil
  "List of (name . meta-var)")

(defun cedille-mode-meta-vars-continue-computation (node &optional allow-locale)
  "Returns t if you should keep computing meta variables in the first child of NODE"
  (when node
    (let* ((keywords (cdr (assoc 'keywords (se-term-data node))))
           (is-application (when keywords (member "application" (split-string keywords " "))))
           (is-locale (when keywords (member "meta-var-locale" (split-string keywords " ")))))
      (and is-application (or allow-locale (not is-locale))))))

(defun cedille-mode-set-assoc-value (alist key new-value)
  "Sets the value of 'KEY in ALIST to NEW-VALUE, or adds it if there was none"
  (append (assq-delete-all key alist) (list (cons key new-value))))

(defun cedille-mode-meta-vars-split (meta-var)
  "Splits the string \"name value\" into (name . value)"
  (let ((split (split-string meta-var " ")))
    (cons (car split) (mapconcat (lambda(x)x) (cdr split) " "))))

(defun cedille-mode-meta-vars-collect (key alist)
  "Collects all values from ALIST with key KEY into a list"
  (when alist
    (if (string= key (caar alist))
        (cons (cedille-mode-meta-vars-split (cdar alist))
              (cedille-mode-meta-vars-collect key (cdr alist)))
      (cedille-mode-meta-vars-collect key (cdr alist)))))

(defun cedille-mode-compute-meta-vars-h (node &optional allow-locale)
  (when (cedille-mode-meta-vars-continue-computation node allow-locale)
    (let* ((data (se-term-data node))
           (introduced-meta-vars (reverse (cedille-mode-meta-vars-collect 'meta-vars-intro data)))
           (solved-meta-vars (reverse (cedille-mode-meta-vars-collect 'meta-vars-sol data)))
           (meta-vars (cedille-mode-compute-meta-vars-h (car (se-node-children node)))))
      (while introduced-meta-vars
        (let* ((name-kind (pop introduced-meta-vars))
               (name (intern (car name-kind)))
               (kind (cdr name-kind))
               (mv (or
                    (cdr (assoc name meta-vars))
                    (make-meta-var
                     :kind kind
                     :file (buffer-file-name)
                     :start-intro (se-term-start node)
                     :end-intro (se-term-end node)))))
          (setq meta-vars (cedille-mode-set-assoc-value meta-vars name mv))))
      (while solved-meta-vars
        (let* ((name-sol (pop solved-meta-vars))
               (name (intern (car name-sol)))
               (sol (cdr name-sol))
               (mv (cdr (assoc name meta-vars)))) ; Assumed to exist
          (setf (meta-var-sol mv) sol
                (meta-var-start-sol mv) (se-term-start node)
                (meta-var-end-sol mv) (se-term-end node))
          (setf (cdr (assoc name meta-vars)) mv)))
      meta-vars)))

(defun cedille-mode-compute-meta-vars()
  "Computes the meta-variables at the current node"
  (when se-mode-selected
    (setq cedille-mode-meta-vars-list
          (cedille-mode-compute-meta-vars-h (se-mode-selected) t))))

(defun cedille-mode-meta-var-text(name mv)
  "Returns the text for the display of a single meta-variable MV"
  (concat
   (se-pin-data 0 (length name) 'loc (list (cons 'fn (meta-var-file mv)) (cons 's (number-to-string (meta-var-start-intro mv))) (cons 'e (number-to-string (meta-var-end-intro mv)))) name)
   " : "
   (meta-var-kind mv)
   (when (meta-var-sol mv)
     (concat
      (se-pin-data 1 2 'loc (list (cons 'fn (meta-var-file mv)) (cons 's (number-to-string (meta-var-start-sol mv))) (cons 'e (number-to-string (meta-var-end-sol mv)))) " = ")
      (meta-var-sol mv)
      ))
   "\n"))

(defun cedille-mode-display-meta-vars()
  (let ((parent cedille-mode-parent-buffer))
    (with-current-buffer (cedille-mode-meta-vars-buffer)
      (setq cedille-mode-parent-buffer parent
            buffer-read-only nil)
      (erase-buffer)
      (let ((meta-vars cedille-mode-meta-vars-list))
        (while meta-vars
          (insert (cedille-mode-meta-var-text (symbol-name (caar meta-vars)) (cdar meta-vars)))
          (setq meta-vars (cdr meta-vars))))
      (goto-char 1)
      (setq buffer-read-only t)
      (setq deactivate-mark nil))))



(defun cedille-mode-meta-vars()
  (cedille-mode-compute-meta-vars)
  (cedille-mode-display-meta-vars)
  (cedille-mode-rebalance-windows))

(defun cedille-mode-meta-vars-buffer-name()
  (with-current-buffer (or cedille-mode-parent-buffer (current-buffer))
    (concat "*cedille-meta-vars-" (file-name-base) "*")))

(defun cedille-mode-meta-vars-buffer()
  (get-buffer-create (cedille-mode-meta-vars-buffer-name)))


(define-minor-mode cedille-meta-vars-mode
  "Creates meta-vars-mode"
  nil
  " Meta-Vars"
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap)
    (define-key map (kbd "m") #'cedille-mode-close-active-window)
    (define-key map (kbd "M") #'cedille-mode-close-active-window)
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "meta-vars mode"))
    map)
  (when cedille-meta-vars-mode
    (set-input-method "Cedille")))

(provide 'cedille-mode-meta-vars)
