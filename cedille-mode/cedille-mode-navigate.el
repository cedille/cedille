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
		    (missing (string= "missing" f))
		    (not-exists (not (file-exists-p f)))
		    (b (if (or missing not-exists) (current-buffer) (find-file f)))
		    (timeline cedille-mode-browsing-history)
		    (past (car cedille-mode-browsing-history))
		    (present this-file))
	       (if not-exists
		   (message "No location at this node")
		 (with-current-buffer b
		   (goto-char n)
		   (unless missing
		     (setq cedille-mode-browsing-history (cons (cons present past) nil))
		     (se-navigation-mode)))
		 ;;; If the mark is active, we are jumping within the buffer. This prevents
                 ;;; a region from being selected.
		 (when mark-active
		   (exchange-point-and-mark 1)
		   (set-mark-command 1))))
	   (message "No location at this node")))
    (message "No node selected")))

(defmacro make-cedille-mode-history-navigate(fwd-p jmp-p)
  "Generates a function for navigating history. fwd-p determines whether the function
moves forward (or backward), and jmp-p determines whether it moves by 
jumping to the ends or moving in single steps."
  `(lambda ()
     (interactive)
     (let ((destfn (lambda (past future) (if ,jmp-p (car (last future)) (car future)))) ;Retrieves the destination we are trying to reach
	   (updatefn (lambda (past present future) ;Updates the timeline after we travel to the destination
		       (setq past (if ,jmp-p (append (cdr (reverse (cons present future))) past) (cons present past)))
		       (setq future (if ,jmp-p nil (cdr future)))
		       (setq cedille-mode-browsing-history (if ,fwd-p (cons past future) (cons future past)))))
	   (navigatefn ;Calls destfn, travels to the retrieved destination, then calls updatefn
	    (lambda (dest-fn update-fn msg)
	      (let* ((timeline cedille-mode-browsing-history)
		     (past (car timeline))
		     (present (buffer-file-name))
		     (future (cdr timeline))
		     (destination (funcall dest-fn past future)))
		(if destination
		    (progn
		      (with-current-buffer (find-file destination) (se-navigation-mode))
		      (funcall update-fn past present future))
		  (message msg))))))
       (funcall navigatefn ;Here is where we call navigatefn with inputs depending on which way we are travelling and how fast
		(lambda (past future) (funcall destfn (if ,fwd-p past future) (if ,fwd-p future past)))
		(lambda (past present future) (funcall updatefn (if ,fwd-p past future) present (if ,fwd-p future past)))
		(concat "You have reached the " (if ,fwd-p "end" "beginning") " of history"))))) ;Error message

(provide 'cedille-mode-navigate)
