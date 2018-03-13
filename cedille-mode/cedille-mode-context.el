; Welcome to the Cedille Mode Context tool!
; This file contains the code that governs the feature allowing the user to retrieve the context at a given point.

					; GLOBAL DEFINITIONS
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

(defcustom cedille-mode-context-shadowed-color "yellow"
  "The color for shadowed variables in context mode"
  :type '(color)
  :group 'cedille-context)

(defvar cedille-mode-context-filtering nil)

(defvar cedille-mode-original-context-list nil)
(defvar cedille-mode-filtered-context-list nil)
(defvar cedille-mode-sorted-context-list nil)

(make-variable-buffer-local
 (defvar cedille-mode-global-context nil
   "The global context surrounding the current file/buffer (used by the beta-reduction buffer)"))

;;; There are three context lists:
;;; 1. The original list (original)
;;; 2. The list after it has been filtered
;;; 3. The list after it has been sorted
;;; This is also the order in which these lists are processed.
;;; First, the original list is derived using cedille-mode-compute-context()
;;; Second, the filtered list is derived using cedille-mode-filter-context()
;;; Finally, the sorted list is derived using cedille-mode-sort-context()
;;; The sorted list is the one displayed to the user.

(defvar cedille-mode-hidden-context-tuples nil
  "Defines a list of tuples corresponding to types/kinds to hide in the context window")

					; HELPER FUNCTIONS
;; Miscellaneous functions that are used repeatedly

(defun cedille-mode-helpers-filter(lst condp)
  "Returns the subset of lst whose members satisfy condp"
  (delete nil (mapcar (lambda (x) (and (funcall condp x) x) (copy-sequence lst)))))

(defun cedille-mode-helpers-has-keyword(entry word)
  "Tests whether context entry has word as a keyword"
  (member word (cdr (assoc 'keywords (cdr entry)))))

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
    (define-key map (kbd "a") (make-cedille-mode-set-variable cedille-mode-context-ordering 'fwd)) 	; a-z ordering
    (define-key map (kbd "z") (make-cedille-mode-set-variable cedille-mode-context-ordering 'bkd)) 	; z-a ordering
    (define-key map (kbd "d") (make-cedille-mode-set-variable cedille-mode-context-ordering 'dn)) 	; parse tree descending
    (define-key map (kbd "u") (make-cedille-mode-set-variable cedille-mode-context-ordering 'up)) 	; parse tree ascending
    (define-key map (kbd "e") (make-cedille-mode-set-variable cedille-mode-context-filtering 'eqnl)) 	; filter 'equational'
    (define-key map (kbd "E") (make-cedille-mode-set-variable cedille-mode-context-filtering 'eqn)) 	; filter 'equation'
    (define-key map (kbd "r") (make-cedille-mode-set-variable cedille-mode-context-filtering nil)) 	; no filter
    (define-key map (kbd "C") #'cedille-mode-close-active-window) 					; exit context mode
    (define-key map (kbd "c") #'cedille-mode-close-active-window) 					; exit context mode
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "context mode")) 			; help page
    (define-key map (kbd "w") #'cedille-mode-toggle-hide-tuple-in-context)				; hide type or kind
    (define-key map (kbd "W") #'cedille-mode-toggle-show-tuples-in-context)				; show all hidden types/kinds
    (define-key map (kbd "$") (make-cedille-mode-customize "cedille-context")) 				; customization page
    (define-key map (kbd "s") (make-cedille-mode-customize-set-variable 'cedille-mode-show-shadowed-variables (not cedille-mode-show-shadowed-variables)))
    map))

(defun cedille-mode-toggle-hide-tuple-in-context()
  "Hides the type or kind associated with the currently selected line"
  (interactive)
  (let* ((line (line-number-at-pos))
	 (context cedille-mode-sorted-context-list)
	 (tuple (cedille-mode-get-tuple-from-position context line))
	 (hidden-list-q 'cedille-mode-hidden-context-tuples))
    (when tuple
      ;; delete selected tuple from list if present or add if not present
      (if (member tuple cedille-mode-hidden-context-tuples)
	  (set hidden-list-q (delete tuple (eval hidden-list-q)))
	(set hidden-list-q (cons tuple (eval hidden-list-q))))
      ;; refresh context buffer
      (other-window 1)
      (cedille-mode-update-buffers)
      (other-window -1)
      (forward-line (- line 1)))))

(defun cedille-mode-toggle-show-tuples-in-context()
  "Show all types and kinds"
  (interactive)
  (setq cedille-mode-hidden-context-tuples nil)
  ;; refresh context buffer
  (let ((line (line-number-at-pos)))
    (other-window 1)
    (cedille-mode-update-buffers)
    (other-window -1)
    (forward-line (- line 1))))

(defun cedille-mode-filter-context()
  "Filters context and stores in cedille-mode-filtered-context-list"
  (let* ((context (copy-sequence cedille-mode-original-context-list))
	 ;; predicate which checks the value of *x* against the value of *cedille-mode-context-filtering*
	 (filterp (lambda (x)
		    (equal cedille-mode-context-filtering x)))
	 ;; given a list and a key, filters out only terms that have that keyword
	 (filter-for-keyword (lambda (lst key)
			       (cedille-mode-helpers-filter lst (lambda (entry)
						     (cedille-mode-helpers-has-keyword entry key)))))
	 ;; filters and returns the input list depending on value of filterp
	 (filter-list (lambda (lst)
			(cond ((funcall filterp 'eqn) (funcall filter-for-keyword lst  "equation"))
			      ((funcall filterp 'eqnl)(funcall filter-for-keyword lst "equational"))
			      (t lst))))
	 (terms (funcall filter-list (car context)))  ; filter terms
	 (types (funcall filter-list (cdr context)))) ; filter types
    ;; set the filtered context list
    (setq cedille-mode-filtered-context-list (cons terms types))))

(defun cedille-mode-sort-context()
  "Sorts context according to ordering and stores in cedille-mode-sorted-context-list"
  (let* ((context (copy-sequence cedille-mode-filtered-context-list))
	 ;; unary predicate for membership in the hidden type/kind list
	 (hidden-p (lambda (pair) (member pair cedille-mode-hidden-context-tuples))) 
	 ;; binary predicate for separating hidden types/kinds
	 (whiteout (lambda (a b) (and (not (funcall hidden-p a)) (funcall hidden-p b))))
	 ;; binary predicate for ascending alphabetical order
	 (string-lt (lambda (a b) (string< (car a) (car b))))
	 ;; binary predicate for descending alphabetical order
	 (string-gt (lambda (a b) (funcall string-lt b a)))
	 ;; predicate checking whether x is equal to context-mode-context-ordering
	 (orderp (lambda (x) (equal cedille-mode-context-ordering x)))
	 ;; sorts the list according to the order specified by context-mode-context-ordering.
	 ;; note that context lists have order 'up when they are first constructed.
	 (sort-list (lambda (list) (sort
				    ;; inner sorting according to specified order
				    (cond ((funcall orderp 'fwd) (sort list string-lt))
					  ((funcall orderp 'bkd) (sort list string-gt))
					  ((funcall orderp 'dn) (reverse list))
					  ((funcall orderp 'up) list))
				    ;; outer sorting sifting hidden types/kinds to bottom
				    whiteout)))
	 (terms (funcall sort-list (car context)))  ; sort terms
	 (types (funcall sort-list (cdr context)))) ; sort types
    ;; set the sorted context list
    (setq cedille-mode-sorted-context-list (cons terms types))))

;; filters the context list, then sorts it
(defun cedille-mode-process-context() (cedille-mode-filter-context) (cedille-mode-sort-context))

					; FUNCTIONS TO COMPUTE THE CONTEXT

(defun cedille-mode-compute-context()
  "Compute the context and store it in local variables in its default order.
The context by default is ordered by parse tree position, from bottom to top."
  (if se-mode-selected
      ;; find the path to the selected point
      (let ((p (se-find-point-path (point) (se-mode-parse-tree))))
	;; set the unmodified context list
	(setq cedille-mode-original-context-list (cedille-mode-get-context p)))))

(defun cedille-mode-span-context (span)
  "Gets the local context for span"
  (setq p (se-find-point-path (se-span-start span) (se-mode-parse-tree)))
  (cedille-mode-get-context p))

(defun my-seq-reduce(f list base-value)
  "Alternative to seq-reduce for versions of emacs lower than 25"
  (if list
      (let ((head (pop list)))
	(my-seq-reduce f list (funcall f base-value head)))
      base-value))

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
  (let* ((terms (car cedille-mode-global-context)) ; Used to be: terms
	 (types (cdr cedille-mode-global-context)) ; Used to be: types
	 ;; adds to each instance (assoc list) in list a predicate indicating if that instance is shadowed
	 ;; this must be done after constructing the initial list so that all instances are considered
	 (add-shadowed (lambda (list)
			 (when list
			   (let*
			       ;; utility function for maximum of list
			       ((maximum (lambda (list) (my-seq-reduce (lambda (acc n) (max acc n)) list 0)))  
				;; compute the maximum number of terms shadowed by this symbol
				(max-shadows (lambda (symbol)
					       (funcall
						maximum
						(mapcar (lambda (alist)
							  (if
							      (string= (car alist) symbol)
							      (cdr (assoc 'shadows alist))
							    0))
							list))))
				;; adds predicate indicating whether instance is shadowed
				(add-is-unshadowed-p (lambda (alist)
						     (let* ((symbol (car alist))
							    (max-shad (funcall max-shadows symbol))
							    (shadows (cdr (assoc 'shadows alist)))
							    ;; only a symbol which is unshadowed can have maximum shadows
							    (is-unshadowed-p (= max-shad shadows)))
						       ;; return the modified instance
						       (append alist (list (list 'is-unshadowed-p is-unshadowed-p)))))))
			     ;; repeat for each instance in the list
			     (mapcar add-is-unshadowed-p list))))))
    (dolist (node (butlast path) (when (or terms types) (cons (funcall add-shadowed terms) (funcall add-shadowed types))))  
      (let ((binder (cdr (assoc 'binder (se-term-data node))))
	    (bound-value (cdr (assoc 'bound-value (se-term-data node))))
	    (children (se-node-children node)))
	;; for each node in the path, only try to add it to the context if it binds something
	(when (and binder children)
	  (let* ((bound (string-to-number binder))
		 (data (se-term-data (nth bound children)))
		 (get (lambda (key) (cdr (assoc key data)))) ; returns data associated with key
		 (symbol (funcall get 'symbol))
		 (type (funcall get 'type))
		 (kind (funcall get 'kind))
		 (keywords-string (funcall get 'keywords))
		 (keywords-list (when keywords-string (split-string keywords-string " " t)))
		 (location (funcall get 'location))
		 (count-shadowed ; counts number of variables shadowed by this one
		  (lambda (lst symbol rec-call) ; string -> nat
		    (if lst
			(let ((this-sym (car (car lst))))
			  (+ (if (equal this-sym symbol) 1 0) (funcall rec-call (cdr lst) symbol rec-call)))
		      0)))
		 (set-list
		  ;; this takes the list to be modified and the type or kind containing the value data
		  (lambda (q-lst value-source) ; quoted list -> list -> nil [mutates input 0]
		    ;; we rename shadowed variables with a [+n] suffix or omit them		    
		    (let* ((shadows (funcall count-shadowed (eval q-lst) symbol count-shadowed)) ; number of symbols shadowed by this one
			   (data (list 
				  (cons 'value value-source) 		; the value displayed for the entry
				  (cons 'bound-value bound-value)       ; the bound value of the variable (only used in let expressions)
				  (cons 'keywords keywords-list) 	; keywords identifying attributes of the entry
				  (cons 'location location)             ; the location of the definition; used in other files, but not this one
				  (cons 'shadows shadows)))) 		; number of symbols shadowed by this one
		      
		      (set q-lst (cons (cons symbol data) (eval q-lst)))))))
	    (when (and symbol (not (equal symbol "_")) (or type kind)) 	; separate types and kinds
	      (if type
		  (funcall set-list 'terms type)
		(funcall set-list 'types kind)))))))))

					; FUNCTIONS TO DISPLAY THE CONTEXT

(defun cedille-mode-display-context()
  "Displays the context"
  (let ((parent cedille-mode-parent-buffer)
        (b (cedille-mode-context-buffer)))
    (cedille-mode-process-context)
    (with-current-buffer b
      (setq buffer-read-only nil
            cedille-mode-parent-buffer parent)
      (erase-buffer)
      (let* ((linedata (cedille-mode-format-context cedille-mode-sorted-context-list))
	     (termdata (car linedata))
	     (typedata (cadr linedata))
	     (println (lambda (line)
			(when line
			  (let* ((color (cadr (assoc 'color line)))
				 (text (cadr (assoc 'text line))))
			    (if color
				(insert (propertize (concat text "\n") 'face `(:foreground ,color)))
			        (insert (concat text "\n"))))))))
	;; print the lines in the context buffer
	(when termdata
	  (insert "==== TERMS ====\n")
	  (mapc println termdata)
	  (when typedata (insert "\n")))
	(when typedata
	  (insert "==== TYPES ====\n")
	  (mapc println typedata)))
      (cedille-mode-highlight-shadowed)
      (goto-char 1)
      ;(fit-window-to-buffer (get-buffer-window b))
      (setq buffer-read-only t)
      (setq deactivate-mark nil))))


(defun cedille-mode-format-context(context) ; -> string
  "Formats the context as text for display"
  (let* ((output) ; defaults to empty string
	 (shadow-p cedille-mode-show-shadowed-variables)
	 ;; formats input pair as "<symbol>:	<value>" ==ACG==
	 ;; filter out shadowed symbols (do not use filter helper for this)
	 (shadow-filter (lambda (lst)
			  (let (shadowed-lst)
			    (dolist (pair (reverse lst) shadowed-lst)
			      (let* ((symbol (car pair))
				     (matches (lambda (thispair) (equal (car thispair) symbol))))
				(setq shadowed-lst (cons pair (remove-if matches shadowed-lst))))))))
	 (loc-prop (lambda (sym loc)
		     (let ((split (split-string loc " - ")))
		       (se-pin-data 1 (length sym) 'loc (list (cons "fn" (car split)) (cons "pos" (cadr split))) sym))))
	 ;; format symbol-value pairs for display
	 (format (lambda (pair)
		   (let* ((hidden-lst cedille-mode-hidden-context-tuples)
			  (symbol (car pair))
			  (data (cdr pair))
			  (is-shadowed-p (not (cadr (assoc 'is-unshadowed-p data))))
			  
			  ;; add dash for erased symbols
			  (fsymbol (concat (if (cedille-mode-helpers-has-keyword pair "noterased") " " "-") symbol))
			  ;; hide types and kinds in whiteout list
			  (fdata (unless (member pair hidden-lst) (cdr (assoc 'value data))))
			  (floc (cdr (assoc 'location data)))
			  (text (concat (funcall loc-prop fsymbol floc) ":\t" fdata))
			  (shadow-c cedille-mode-context-shadowed-color)
			  (color (when is-shadowed-p shadow-c)))
		     ;; output is an association list detailing the formatting for the given line
		     (list
		      (list 'color color)
		      (list 'text text)))))
	 ;; utility function to apply the shadow filter if applicable
	 (apply-shadow-filter-optionally (lambda (list)
				(if shadow-p
				    list
				  (funcall shadow-filter list))))
	 
	 (terms (funcall apply-shadow-filter-optionally (car context)))
	 (types (funcall apply-shadow-filter-optionally (cdr context))))
    ;; return a pair where first element is list of formatted terms and second is list of formatted types
  (list
   (mapcar format terms)
   (mapcar format types))))
    

					; CONVENIENT FUNCTIONS

(defun cedille-mode-get-tuple-from-position(context line)
  "Returns the tuple of the context corresponding with given line"
  (let* ((terms (car context))
	 (types (cdr context))
	 ;; The start and end positions of term/type are hardcoded from
	 ;;   cedille-mode-format-context
	 ;; If that changes, you will need to change these values as well.
	 (terms-start (if terms 2 0))
	 (terms-end (if terms (+ 1 (length terms)) 0))
	 (types-start (if terms (+ terms-end 3) 2))
	 (types-end (+ types-start (length types) -1))
	 (interval (lambda (x left right) (and (>= x left) (<= x right))))
	 (tuple-index
	  ;; map the actual line number to the appropriate list index
	  (if (funcall interval line terms-start terms-end) (- line 2)
	    (if (funcall interval line types-start types-end) (- line 4)
	      -1)))
	 (tuples (append terms types)))
    (if (>= tuple-index 0)
	(nth tuple-index tuples)
      ;; if cursor is not on a line with a type/kind, don't do anything
      nil)))

(defun cedille-mode-context()
  (cedille-mode-compute-context)
  (cedille-mode-display-context)
  (cedille-mode-rebalance-windows))

(defun cedille-mode-context-buffer-name() (concat "*cedille-context-" (file-name-base) "*"))

(defun cedille-mode-context-buffer() "Retrieves the context buffer" (get-buffer-create (cedille-mode-context-buffer-name)))

(provide 'cedille-mode-context)
