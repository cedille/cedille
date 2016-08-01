; Welcome to the Cedille Mode Context tool!
; This file contains the code that governs the feature allowing the user to retrieve the context at a given point.


					; MINOR MODE FUNCTIONS

(define-minor-mode cedille-context-view-mode
  "Creates context mode, which displays the context of the selected node"
  nil         ; init-value, whether the mode is on automatically after definition
  " Context"  ; indicator for mode line
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "a") #'cedille-mode-context-order-fwd) ; a-z ordering
    (define-key map (kbd "z") #'cedille-mode-context-order-bkd) ; z-a ordering
    (define-key map (kbd "d") #'cedille-mode-context-order-def) ; default ordering
    (define-key map (kbd "C") #'cedille-mode-close-context-window) ; exit context mode
    (define-key map (kbd "c") #'cedille-mode-close-context-window) ; exit context mode
    map
    )
  )

(defun cedille-mode-context-order-fwd()
  "Sorts the context alphabetically (forward)"
  (interactive)
  (with-current-buffer (cedille-mode-context-buffer)
    (setq context-ordering 'fwd)
    (make-local-variable 'context-ordering)
    (let* ((context context-original-list)
	   (terms (sort (car context) '<))
	   (types (sort (cdr context) '<)))
      (setq context-list (cons terms types))
      (make-local-variable context-list))))

(defun cedille-mode-context-order-bkd()
  "Sorts the context alphabetically (backward)"
  (interactive)
  (with-current-buffer (cedille-mode-context-buffer)
    (setq context-ordering 'bkd)
    (make-local-variable 'context-ordering)
    (let* ((context context-original-list)
	   (terms (sort (car context) '>))
	   (types (sort (cdr context) '>)))
      (setq context-list (cons terms types))
      (make-local-variable 'context-list))))

(defun cedille-mode-context-order-def()
  "Restores default context ordering"
  (interactive)
  (setq context-ordering nil)
  (make-local-variable 'context-ordering)
  (with-current-buffer (cedille-mode-context-buffer)
    (setq context-list context-original-list)
    (make-local-variable 'context-list)))

					; FUNCTIONS TO COMPUTE THE CONTEXT

(defun cedille-mode-compute-context()
  "Compute the context and store it in local variables"
  (interactive)
  (if se-mode-selected
      ;Retrieve context from parse tree
      (let ((b (cedille-mode-context-buffer))
	    (p (se-find-point-path (point) (se-mode-parse-tree))))
	;Initialize context minor mode and store context in local variables
	(with-current-buffer b
	  (setq context-original-list (cedille-mode-get-context p))
	  (setq context-list context-original-list)
	  (make-local-variable 'context-original-list)
	  (make-local-variable 'context-list)
	  (cedille-context-view-mode)))))

(defun cedille-mode-get-context(path) ; -> ( list<(string,string)>, list<(string,string) )
  "Returns a tuple consisting of:
   1. a list of terms and their associated types
   2. a list of types and their associated kinds"
  (let (terms
	types)
    (while path ;Recursively traverse the path
      (let ((binder (cdr (assoc 'binder (se-term-data (car path)))))
	    (children (se-node-children (car path))))
	(if (and binder children)
	    (let* ((bound (string-to-number binder)) 
		   (data (se-term-data (nth bound children))) ;Get data from the child node matchng the binder number
		   (symbol (cdr (assoc 'symbol data)))
		   (kind (cdr (assoc 'kind data)))
		   (type (cdr (assoc 'type data))))
	      (if (and symbol (not (equal symbol "_"))) ;Classify the symbol as a term or a type and add it to the appropriate list. Ignore '_' symbols 
		  (if type
		      (setq terms (cons (cons symbol type) terms))
		    (if kind
			(setq types (cons (cons symbol kind) types))))))))
      (setq path (cdr path)))
    (cons terms types))) ;Return a tuple consisting of the term-type pairs and the type-kind pairs

					; FUNCTIONS TO DISPLAY THE CONTEXT

(defun cedille-mode-display-context()
  "Displays the context"
  (let ((b (cedille-mode-context-buffer)))
    (with-current-buffer b
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert (cedille-mode-format-context context-list))
      (goto-char 1)
      (fit-window-to-buffer (get-buffer-window b))
      (setq buffer-read-only t)
      (setq deactivate-mark nil))))

(defun cedille-mode-format-context(context) ; -> string
  "Formats the context as text for display"
  (let ((output ""))
    (let ((terms (car context))
	  (types (cdr context)))
      (if (or terms types)
	  (progn
	    (if terms ;Print out the terms and their types
		(progn
		  (setq output (concat output "==== TERMS ====\n"))
		  (while terms
		    (let* ((head (car terms))
			   (symbol (car head))
			   (value (cdr head)))
		      (setq output (concat output symbol ":\t" value "\n"))
		      (setq terms (cdr terms))))
		  (setq output (concat output "\n"))))
	    (if types ;Print out the types and their kinds
		(progn
		  (setq output (concat output  "==== TYPES ====\n"))
		  (while types
		    (let* ((head (car types))
			   (symbol (car head))
			   (value (cdr head)))
		      (setq output (concat output symbol ":\t" value "\n"))
		      (setq types (cdr types))))))
	    output)
	"Selected context is empty."))))
	  
					; CONVENIENT FUNCTIONS

(defun cedille-mode-context()
  (cedille-mode-compute-context)
  (cedille-mode-display-context))

(defun cedille-mode-context-buffer-name() (concat "*cedille-context-" (file-name-base (buffer-name))))

(defun cedille-mode-context-buffer()
  "Retrieves the context buffer"
  (get-buffer-create (cedille-mode-context-buffer-name)))

(defun cedille-mode-context-window()
  "Retrieves (or creates) the context window"
  (let* ((context-buffer (cedille-mode-context-buffer))
	 (context-window (get-buffer-window context-buffer)))
    (if context-window
	context-window
      (split-window))))

(defun cedille-mode-jump-to-context-window()
  "Toggles context mode on/off"
  (interactive)
  (if se-mode-selected
      (let* ((first-buffer (current-buffer))
	     (context-buffer (cedille-mode-context-buffer))
	     (context-window (get-buffer-window context-buffer)))
	(if context-window
	    ;If there is a context mode window, delete it
	    (delete-window context-window)
	  ;Else create a new one
	  (cedille-mode-context)
	  (set-window-buffer (cedille-mode-context-window) context-buffer)
	  (fit-window-to-buffer (get-buffer-window context-buffer))
	  (select-window (get-buffer-window context-buffer))))))

(defun cedille-mode-close-context-window()
  (interactive)
  (delete-window))
;  (let* ((context-buffer (cedille-mode-context-buffer))
;	 (context-window (get-buffer-window context-buffer)))
 ;   (if context-window
;	;If there is a context mode window, delete it
;	(delete-window context-window))))

					; FUNCTION TO CALL WHEN HOTKEY IS PRESSED

(defun cedille-mode-toggle-context-mode()
  "Toggles context mode on/off"
  (interactive)
  (if se-mode-selected
      (let* ((first-buffer (current-buffer))
	     (context-buffer (cedille-mode-context-buffer))
	     (context-window (get-buffer-window context-buffer)))
	(if context-window
	    ;If there is a context mode window, delete it
	    (delete-window context-window)
	  ;Else create a new one
	  (cedille-mode-context)
	  (set-window-buffer (cedille-mode-context-window) context-buffer)
	  (fit-window-to-buffer (get-buffer-window context-buffer))))))
      
(provide 'cedille-mode-context)
