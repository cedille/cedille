; Contains the functions for retrieving the context at a given point.

(defun cedille-mode-get-context(path) ; -> ( list<(string,string)>, list<(string,string) )
  "Returns a tuple consisting of:
   1. a list of symbols and their associated types
   2. a list of symbols and their associated kinds"
  (let (terms
	types)
    (while path
      (let ((binder (cdr (assoc 'binder (se-term-data (car path)))))
	    (children (se-node-children (car path))))
	(if (and binder children)
	    (let* ((bound (string-to-number binder))
		   (data (se-term-data (nth bound children)))
		   (symbol (cdr (assoc 'symbol data)))
		   (kind (cdr (assoc 'kind data)))
		   (type (cdr (assoc 'type data))))
	      (if symbol
		  (if type
		      (setq terms (cons (cons symbol type) terms))
		    (if kind
			(setq types (cons (cons symbol kind) types))))))))
      (setq path (cdr path)))
    (cons terms types)))

(defun cedille-mode-format-context(path) ; -> string
  "Formats the context as text for display"
  (let ((output "")
	(context (cedille-mode-get-context path)))
    (let ((terms (car context))
	  (types (cdr context)))
      (if (or terms types)
	  (progn
	    (if terms
		(progn
		  (setq output (concat output "==== TERMS ====\n"))
		  (while terms
		    (let* ((head (car terms))
			   (symbol (car head))
			   (value (cdr head)))
		      (setq output (concat output symbol ":\t" value "\n"))
		      (setq terms (cdr terms))))
		  (setq output (concat output "\n"))))
	    (if types (setq output (concat output  "==== TYPES ====\n")))
	    (while types
	      (let* ((head (car types))
		     (symbol (car head))
		     (value (cdr head)))
		(setq output (concat output symbol ":\t" value "\n"))
		(setq types (cdr types))))
	    output)
	"Selected context is empty."))))

(defun cedille-mode-context()
  "Shows the context for the current node. This is the function that should be called when the user presses 'c'."
  (interactive)
  (if se-mode-selected
      (let* ((b (cedille-info-buffer))
	     (d (se-term-to-json (se-mode-selected)))
	     (p (se-find-point-path (point) (se-mode-parse-tree)))
	     (second (cdr p))
	     )
	(with-current-buffer b
	  (erase-buffer)
	  (insert (cedille-mode-format-context second)))
	(cedille-adjust-info-window-size)
	(setq deactivate-mark nil))))

(provide 'cedille-mode-context)
