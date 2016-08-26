;;; =====================================
;;; Implement top-level definitions view
;;; =====================================
;;;
;;; cedille-mode.el changes to make
;;;
;;; Load the file (somewhere past the navigation commands):
;;; (load "incoming/cjr-cedille-mode-summary")
;;;
;;; Add key to activate:
;;; (se-navi-define-key 'cedille-mode (kbd "S") #'cedille-mode-summary-display)
;;;

(load-library "cedille-mode-parent")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary retrieval code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-get-all-summaries()
  "Return the pair of the list of summaries for the current spans and the list of the corresponding start positions"
  (let ((helper (lambda (spans summary-list start-pos-list rec-fn) ; the last argument allows for a recursive call to helper
		 (if spans
		     (let* ((first-span (car spans))
			    (summary (assoc 'summary (se-span-data first-span))))
		       (if summary
			   (funcall rec-fn (cdr spans) (cons (cdr summary) summary-list) 
				      (cons (se-span-start first-span) start-pos-list) rec-fn)
			 (funcall rec-fn (cdr spans) summary-list start-pos-list rec-fn)))
		   (cons (reverse summary-list) (reverse start-pos-list)))))) ;reversed to keep in same order as file
    (funcall helper se-mode-spans nil nil helper)))

(defun cedille-mode-summary-list-to-string(summaries)
  "Convert the list of summaries into a single string"
  (let ((helper (lambda (summaries str rec-fn)
		  (if summaries
		      (funcall rec-fn (cdr summaries) (concat str "\n" (car summaries)) rec-fn)
		    (substring str 1))))) ; removes initial newline -- bad solution for empty file
    (replace-regexp-in-string "^ctor" " " (funcall helper summaries "" helper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary View minor-mode code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-get-start-position()
  "Gets the start position from the start-list using the current line number"
  (let ((helper (lambda (linenum start-list rec-fn) ;last argument allows recursive call to helper
		  (if (eq linenum 1)
		      (car start-list)
		    (funcall rec-fn (- linenum 1) (cdr start-list) rec-fn)))))
    (funcall helper (string-to-number (car (cdr (split-string (what-line) " ")))) cedille-mode-start-list helper)))

(defun cedille-mode-summary-jump()
  "Jumps from the summary of a top-level definition to that definition"
    (interactive)
    (let ((start-pos (cedille-mode-get-start-position)))
        (select-window (get-buffer-window cedille-mode-main-buffer))
        (goto-char start-pos)
        (se-navigation-mode)
        ; the following prevents highlighting errors when jumping to navigation mode buffer, copied from nav-jump
        (if mark-active                                                                 
            (progn                                                                      
                (exchange-point-and-mark 1)                                                   
                (set-mark-command 1)))
        (message (concat "Jump to char:  " (number-to-string start-pos)))))

(define-minor-mode cedille-summary-view-mode
    "Creates summary mode, which allows jumping from a summary back to its top-level definition in the main window"
    nil         ; init-value, whether the mode is on automatically after definition
    " Summary"  ; indicator for mode line
    (let ((map (make-sparse-keymap)))
      (set-keymap-parent map cedille-mode-minor-mode-parent-keymap) ; inherit bindings from parent keymap
      (define-key map (kbd "j") 'cedille-mode-summary-jump)         ; jump to selected line
      (define-key map (kbd "s") #'cedille-mode-close-active-window) ; close summary mode
      (define-key map (kbd "S") #'cedille-mode-close-active-window) ; close summary mode
      map))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary View display code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-summary-buffer-name()
  "Generates a unique name for each file's summary"
    (concat "*cedille-summary-" (file-name-base) "*"))

(defun cedille-mode-summary-buffer()
  "Creates/gets and returns the summary buffer"
    (get-buffer-create (cedille-mode-summary-buffer-name)))

(defun cedille-mode-summary()
  (let* ((summary-buffer (cedille-mode-summary-buffer))
	 (summary-pair (cedille-mode-get-all-summaries))
	 (summary-string (cedille-mode-summary-list-to-string (car summary-pair)))
	 (summary-starts (cdr summary-pair))
	 (main-buffer (current-buffer)))
    (with-current-buffer summary-buffer
      (setq buffer-read-only nil) 
      (erase-buffer)
      (insert summary-string)
      (setq buffer-read-only t)
      ;; variables set for use in summary minor mode
      (setq cedille-mode-start-list summary-starts)
      (make-local-variable 'cedille-mode-start-list)
      (setq cedille-mode-main-buffer main-buffer)
      (make-local-variable 'cedille-mode-main-buffer))
    (cedille-mode-rebalance-windows)))

(provide 'cedille-mode-summary)
