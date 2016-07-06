; Contains the functions for retrieving the context at a given point.

(defun cedille-mode-get-context(path) ; -> ( list<(string,string)>, list<(string,string) )
  "Returns a tuple consisting of:
   1. a list of symbols and their associated types
   2. a list of symbols and their associated kinds"
  (let (types
	kinds)
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
		      (setq types (cons (cons symbol type) types))
		    (if kind
			(setq kinds (cons (cons symbol kind) kinds))))))))
      (setq path (cdr path)))
    (cons types kinds)))

(defun cedille-mode-format-context(path) ; -> string
  "Formats the context as text for display"
  (let ((output "")
	(context (cedille-mode-get-context path)))
    (let ((types (car context))
	  (kinds (cdr context)))
      (if (or types kinds)
	  (progn
	    (if types
		(progn
		  (setq output (concat output "==== TYPES ====\n"))
		  (while types
		    (let* ((head (car types))
			   (symbol (car head))
			   (value (cdr head)))
		      (setq output (concat output symbol ":\t" value "\n"))
		      (setq types (cdr types))))
		  (setq output (concat output "\n"))))
	    (if kinds (setq output (concat output  "==== KINDS ====\n")))
	    (while kinds
	      (let* ((head (car kinds))
		     (symbol (car head))
		     (value (cdr head)))
		(setq output (concat output symbol ":\t" value "\n"))
		(setq kinds (cdr kinds))))
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
