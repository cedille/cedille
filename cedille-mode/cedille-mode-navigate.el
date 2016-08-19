;;; Contains the jump function and history navigation functions

(defun cedille-mode-jump()
  "Jumps to a location associated with the selected node"
  (interactive)  
  (if se-mode-selected
      (let* ((d (se-term-data (se-mode-selected)))
	     (lp (assoc 'location d))
	     (this-file (buffer-file-name)))
	 (if lp 
	     (let* ((l (cdr lp))
		    (ls (split-string l " - "))
		    (f (car ls))
		    (n (string-to-number (cadr ls)))
		    (b (find-file f))
		    (timeline cedille-mode-browsing-history)
		    (past (car cedille-mode-browsing-history))
		    (present (cons this-file (point))))
	       (setq cedille-mode-browsing-history (cons (cons present past) '(nil nil)))
	       (with-current-buffer b (goto-char n) (se-navigation-mode)))
	   (message "No location at this node")))
    (message "No node selected"))
  ;;; If the mark is active, we are jumping within the buffer. This prevents
  ;;; a region from being selected.
  (if mark-active
      (progn
	(exchange-point-and-mark 1)
	(set-mark-command 1))))

(defmacro make-cedille-mode-history-navigate(dest-fn update-fn msg)
  "Takes as input a function to retrieve the destination file by name 
and a function to update the timeline and a message:\n
dest-fn: past -> future -> destination\n
update-fn: past -> future -> nil [mutates cedille-mode-browsing-history]\n
msg: a message to display if it is not possible to move"
  `(let* ((timeline cedille-mode-browsing-history)
	  (past (car timeline))
	  (present (cons (buffer-file-name) (point)))
	  (future (cdr timeline))
	  (destination (,dest-fn past future))
	  (dest-file (car destination))
	  (dest-line (cdr destination)))
     (if dest-file
	 (progn
	   (with-current-buffer (find-file dest-file)
	     (goto-char dest-line)
	     (se-navigation-mode))
	   (,update-fn past present future))
       (message ,msg))))
	  
(defun cedille-mode-history-beginning()
  "Jump to start of history"
  (interactive)
  (make-cedille-mode-history-navigate
   (lambda(past future) (car (last past 3)))
   (lambda (past present future)
     (setq future (append (cdr (reverse (cons present (butlast past 2)))) future))
     (setq past '(nil nil))
     (setq cedille-mode-browsing-history (cons past future)))
   "You have reached the beginning of history"))

(defun cedille-mode-history-end()
  "Jump to end of history"
  (interactive)
  (make-cedille-mode-history-navigate
   (lambda(past future) (car (last future 3)))
   (lambda(past present future)
     (setq past (append (cdr (reverse (cons present (butlast future 2)))) past))
     (setq future '(nil nil))
     (setq cedille-mode-browsing-history (cons past future)))
   "You have reached the end of history"))

(defun cedille-mode-history-backward()
  "Retreat backward in browsing history"
  (interactive)
  (make-cedille-mode-history-navigate
   (lambda(past future) (car past))
   (lambda(past present future)
     (setq past (cdr past))
     (setq future (cons present future))
     (setq cedille-mode-browsing-history (cons past future)))
   "You have reached the beginning of history"))

(defun cedille-mode-history-forward()
  "Advance forward in browsing history"
  (interactive)
  (make-cedille-mode-history-navigate
   (lambda(past future) (car future))
   (lambda(past present future)
     (setq past (cons present past))
     (setq future (cdr future))
     (setq cedille-mode-browsing-history (cons past future)))
   "You have reached the end of history"))

(provide 'cedille-mode-navigate)
