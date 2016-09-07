; Welcome to the Cedille Mode Context tool!
; This file contains the code that governs the feature allowing the user to retrieve the context at a given point.


					; GLOBAL DEFINITIONS
(load-library "cedille-mode-customize")
(load-library "cedille-mode-info")
(load-library "cedille-mode-parent")

(defgroup cedille-context nil
  "Context options for Cedille"
  :group 'cedille)

(defcustom cedille-mode-context-ordering 'fwd
  "Default ordering of context mode"
  :type '(radio (const :tag "A - Z" fwd)
		(const :tag "Z - A" bkd)
		(const :tag "Parse tree descending" dn)
		(const :tag "Parse tree ascending" up))
  :group 'cedille-context)

(defcustom cedille-mode-show-shadowed-variables nil
  "Controls whether or not shadowed variables are displayed in context."
  :type '(boolean)
  :group 'cedille-context)

(defvar cedille-mode-context-filtering nil)

(defvar cedille-mode-original-context-list)
(defvar cedille-mode-filtered-context-list)
(defvar cedille-mode-sorted-context-list)

;;; There are three context lists:
;;; 1. The original list (original)
;;; 2. The list after it has been filtered
;;; 3. The list after it has been sorted
;;; This is also the order in which these lists are processed.
;;; First, the original list is derived using cedille-mode-compute-context()
;;; Second, the filtered list is derived using cedille-mode-filter-context()
;;; Finally, the sorted list is derived using cedille-mode-sort-context()
;;; The sorted list is the one displayed to the user.

					; MINOR MODE FUNCTIONS

;; Note for future refactoring: these can be combined if filters are not a toggle

(defmacro make-cedille-mode-set-variable(variable value)
  `(lambda()
     (interactive)
     (setq ,variable ,value)
     (other-window 1)
     (cedille-mode-update-buffers)
     (other-window -1)))

(defmacro make-cedille-mode-customize-set-variable(custom-variable value)
  `(lambda()
     (interactive)
     (customize-set-variable ,custom-variable ,value)
     (other-window 1)
     (cedille-mode-update-buffers)
     (other-window -1)))

(define-minor-mode cedille-context-view-mode
  "Creates context mode, which displays the context of the selected node"
  nil         ; init-value, whether the mode is on automatically after definition
  " Context"  ; indicator for mode line
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap) ; inherit bindings from parent keymap
    (define-key map (kbd "a") (make-cedille-mode-set-variable cedille-mode-context-ordering 'fwd)) ; a-z ordering
    (define-key map (kbd "z") (make-cedille-mode-set-variable cedille-mode-context-ordering 'bkd)) ; z-a ordering
    (define-key map (kbd "d") (make-cedille-mode-set-variable cedille-mode-context-ordering 'dn)) ; parse tree descending
    (define-key map (kbd "u") (make-cedille-mode-set-variable cedille-mode-context-ordering 'up)) ; parse tree ascending
    (define-key map (kbd "e") (make-cedille-mode-set-variable cedille-mode-context-filtering 'eqnl)) ; filter 'equational'
    (define-key map (kbd "E") (make-cedille-mode-set-variable cedille-mode-context-filtering 'eqn)) ; filter 'equation'
    (define-key map (kbd "f") (make-cedille-mode-set-variable cedille-mode-context-filtering nil)) ; no filter
    (define-key map (kbd "C") #'cedille-mode-close-active-window) ; exit context mode
    (define-key map (kbd "c") #'cedille-mode-close-active-window) ; exit context mode
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "context mode")) ;help page
    (define-key map (kbd "$") (make-cedille-mode-customize "cedille-context")) ;customization page
    (define-key map (kbd "s") (make-cedille-mode-customize-set-variable 'cedille-mode-show-shadowed-variables (not cedille-mode-show-shadowed-variables)))
    map))

  

(defun cedille-mode-filter-context()
  "Filters context and stores in cedille-mode-filtered-context-list"
  (let* ((context (copy-sequence cedille-mode-original-context-list))
	 (filter (lambda (lst condp) (delete nil (mapcar (lambda (x) (and (funcall condp x) x)) (copy-sequence lst))))) ; returns a list of objects satisfying condp
	 (has-keyword (lambda (entry word) (member word (cdr (assoc 'keywords (cdr entry)))))) ; tests whether a context entry has keyword associated with it
	 (filterp (lambda (x) (equal cedille-mode-context-filtering x))) ; checks the value of x against the context-filtering variable
	 (filter-for-keyword (lambda (lst key) (funcall filter lst (lambda (entry) (funcall has-keyword entry key))))) ; for brevity
	 (filter-list (lambda (lst) (cond ((funcall filterp 'eqn) (funcall filter-for-keyword lst  "equation")) ; filters and returns input list
					  ((funcall filterp 'eqnl) (funcall filter-for-keyword lst "equational"))
					  (t lst))))
	 (terms (funcall filter-list (car context)))
	 (types (funcall filter-list (cdr context))))
    (setq cedille-mode-filtered-context-list (cons terms types))))

(defun cedille-mode-sort-context()
  "Sorts context according to ordering and stores in cedille-mode-sorted-context-list"
  (let* ((context (copy-sequence cedille-mode-filtered-context-list))
	 (string-lt (lambda (a b) (string< (car a) (car b)))) ; ascending alphabetical order
	 (string-gt (lambda (a b) (funcall string-lt b a))) ; descending alphabetical order
	 (orderp (lambda (x) (equal cedille-mode-context-ordering x))) ;checks the value of x against the context-ordering variable
	 (sort-list (lambda (list) (cond ((funcall orderp 'fwd) (sort list string-lt)) ; sorts and returns the input list
					 ((funcall orderp 'bkd) (sort list string-gt))
					 ((funcall orderp 'dn) (reverse list))
					 ((funcall orderp 'up) list))))
	 (terms (funcall sort-list (car context)))
	 (types (funcall sort-list (cdr context))))
    (setq cedille-mode-sorted-context-list (cons terms types))))

(defun cedille-mode-process-context() (cedille-mode-filter-context) (cedille-mode-sort-context))

					; FUNCTIONS TO COMPUTE THE CONTEXT

(defun cedille-mode-compute-context()
  "Compute the context and store it in local variables in its default order.
The context by default is ordered by parse tree position, from bottom to top."
  (if se-mode-selected
      (let ((p (se-find-point-path (point) (se-mode-parse-tree))))
	(setq cedille-mode-original-context-list (cedille-mode-get-context p))))) ;Store the unmodified context.

(defun cedille-mode-get-context(path) ; -> list <context>
  "Searches the input path for binder nodes, returning a tuple consisting of:\n
1. A list of term symbols and their types and keywords\n
2. A list of type symbols and their kinds and keywords\n
The output is a tuple (terms types)\n
where each object is a tuple (symbol alist)\n
where alist is an association list containing the info associated with symbol\n
which currently consists of:\n
+ 'value' : the type or kind of symbol
+ 'keywords': a list of keywords associated with symbol"
  (let (terms types)
    (dolist (node path (when (or terms types) (cons terms types)))
      ;; for each node in the path, we are going to see if it binds a symbol and add it to the output list if it does
      (let ((binder (cdr (assoc 'binder (se-term-data node))))
	    (children (se-node-children node)))
	(when (and binder children)
	  (let* ((bound (string-to-number binder)) ; for readability
		 (data (se-term-data (nth bound children)))
		 (symbol (cdr (assoc 'symbol data)))
		 (type (cdr (assoc 'type data)))
		 (kind (cdr (assoc 'kind data)))
		 (keywords-string (cdr (assoc 'keywords data))) ; for readability
		 (keywords-list (when keywords-string (split-string keywords-string " " t)))
		 ;; to rename the shadowed variables, we will use name-symbol and count-original-symbols
		 (count-original-symbols
		  ;; recursively counts how many instances of the given original symbol already occur in the list
		  (lambda (lst original-symbol rec-call) ; list -> string -> nat
		    (if lst
			(let ((os (cdr (assoc 'original-symbol (cdr (car lst)))))) ;os is the symbol of the entry in the list
			  (+ (if (equal os original-symbol) 1 0) (funcall rec-call (cdr lst) original-symbol rec-call)))
		      0)))
		 (name-symbol 
		  (lambda (lst original-symbol) ; list -> string -> string
		    (let ((count (funcall count-original-symbols lst original-symbol count-original-symbols)))
		      (concat original-symbol "[+" (number-to-string count) "]"))))
		 
		 (set-list ; for brevity
		  ;; this takes the list to be modified and the type or kind containing the value data
		  (lambda (q-lst value-source) ; quoted list -> list -> nil [mutates input 0]
		    ;; we rename shadowed variables with a [+n] suffix or omit them
		    ;;cedille-mode-show-shadowed-variables
		    (let ((data (list ; for brevity - this is the data associated with the symbol
				 (cons 'value value-source) ; the value displayed for the entry
				 (cons 'keywords keywords-list) ; keywords identifying attributes of the entry
				 (cons 'original-symbol symbol))) ; the original symbol identifying the entry
			  (shadow-p cedille-mode-show-shadowed-variables
				    )) ; for brevity
		      (set q-lst (cons (cons
					(if shadow-p (funcall name-symbol (eval q-lst) symbol) symbol)
					data)
				       (if shadow-p (eval q-lst) (delq (assoc symbol (eval q-lst)) (eval q-lst)))))))))
	    (when (and symbol (not (equal symbol "_")) (or type kind)) ;separate types and kinds
	      (if type (funcall set-list 'terms type) (funcall set-list 'types kind)))))))))

					; FUNCTIONS TO DISPLAY THE CONTEXT

(defun cedille-mode-display-context()
  "Displays the context"
  (let ((b (cedille-mode-context-buffer)))
    (cedille-mode-process-context)
    (with-current-buffer b
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert (cedille-mode-format-context cedille-mode-sorted-context-list))
      (goto-char 1)
      (fit-window-to-buffer (get-buffer-window b))
      (setq buffer-read-only t)
      (setq deactivate-mark nil))))

(defun cedille-mode-format-context(context) ; -> string
  "Formats the context as text for display"
  (let ((output) ;""
	(format (lambda (pair) (concat (car pair) ":\t" (cdr (assoc 'value (cdr pair))))))
	(terms (car context))
	(types (cdr context)))
    (if (or terms types)
	(progn
	  (when terms ;Print out the terms and their types
	    (setq output (concat "==== TERMS ====\n" (mapconcat format terms "\n") (when types "\n\n"))))
	  (when types ;Print out the types and their kinds
	    (setq output (concat output "==== TYPES ====\n" (mapconcat format types "\n"))))
	  output)
      "Selected context is empty.")))

					; CONVENIENT FUNCTIONS

(defun cedille-mode-context()
  (cedille-mode-compute-context)
  (cedille-mode-display-context)
  (cedille-mode-rebalance-windows))

(defun cedille-mode-context-buffer-name() (concat "*cedille-context-" (file-name-base (buffer-name)) "*"))

(defun cedille-mode-context-buffer() "Retrieves the context buffer" (get-buffer-create (cedille-mode-context-buffer-name)))

(provide 'cedille-mode-context)
