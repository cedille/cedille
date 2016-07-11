; Welcome to the Cedille Mode Context tool!
; This file contains the code that governs the feature allowing the user to retrieve the context at a given point.

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

(defun cedille-mode-format-context(path) ; -> string
  "Formats the context as text for display"
  (let ((output "")
	(context (cedille-mode-get-context path)))
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

(defun cedille-mode-context()
  "Shows the context for the current node. This is the function that should be called when the user presses 'c'."
  (interactive)
  (if se-mode-selected
      (let ((b (get-buffer-create (cedille-mode-context-buffer-name)))
	    (p (se-find-point-path (point) (se-mode-parse-tree))))
	(with-current-buffer b
	  (erase-buffer)
	  (insert (cedille-mode-format-context p)))
	(setq deactivate-mark nil))))

(defun cedille-mode-context-buffer-name() (concat "*cedille-context-" (file-name-base (buffer-name))))

(defun cedille-mode-toggle-context-mode()
  "Toggles context mode on/off"
  (interactive)
  (let ((context-buffer (get-buffer-create (cedille-mode-context-buffer-name))))
    (if (get-buffer-window context-buffer)
	;If there is a context mode window, erase it
	(delete-window (get-buffer-window context-buffer))
      ;Else create a new one
      (cedille-mode-context)
      (display-buffer context-buffer))))

(provide 'cedille-mode-context)
