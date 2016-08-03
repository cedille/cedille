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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary retrieval code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-get-all-summaries-helper(spans summary-list start-pos-list)
    (if spans
        (let* ((first-span (car spans))
                (summary (assoc 'summary (se-span-data first-span))))
            (if summary
                (cedille-mode-get-all-summaries-helper (cdr spans) (cons (cdr summary) summary-list) 
                            (cons (se-span-start first-span) start-pos-list))
                (cedille-mode-get-all-summaries-helper (cdr spans) summary-list start-pos-list)
            )
        )
        (cons (reverse summary-list) (reverse start-pos-list)) ;reversed to keep in same order as file
    )
)

(defun cedille-mode-get-all-summaries()
  "Return the pair of the list of summaries for the current spans and the list of the corresponding start positions"
    (cedille-mode-get-all-summaries-helper se-mode-spans nil nil)
)

(defun cedille-mode-summary-list-to-string-helper(summaries str)
    (if summaries
        (cedille-mode-summary-list-to-string-helper (cdr summaries) (concat str "\n" (car summaries)))
        (substring str 1) ; removes initial newline -- bad solution for empty file
    )
)

(defun cedille-mode-summary-list-to-string(summaries)
  "Convert the list of summaries into a single string"
    (replace-regexp-in-string "^ctor" " " (cedille-mode-summary-list-to-string-helper summaries ""))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary View minor-mode code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-get-start-position-helper(linenum start-list)
   (if (eq linenum 1)
        (car start-list)
        (cedille-mode-get-start-position-helper (- linenum 1) (cdr start-list))
   )
)

(defun cedille-mode-get-start-position()
  "Gets the start position from the start-list using the current line number"
    (cedille-mode-get-start-position-helper (string-to-number (car (cdr (split-string (what-line) " ")))) cedille-mode-start-list)
)

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
                (set-mark-command 1)
            )
        )
        (message (concat "Jump to char:  " (number-to-string start-pos)))
    )
)

(define-minor-mode cedille-summary-view-mode
    "Creates summary mode, which allows jumping from a summary back to its top-level definition in the main window"
    nil         ; init-value, whether the mode is on automatically after definition
    " Summary"  ; indicator for mode line
    (let ((map (make-sparse-keymap)))
        (define-key map (kbd "j") 'cedille-mode-summary-jump)
        map
    )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;     Summary View display code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cedille-mode-get-summary-buffer-name()
  "Generates a unique name for each file's summary"
    (concat "*cedille-summary-" (file-name-base) "*")
)

(defun cedille-mode-get-summary-buffer()
  "Creates/gets and returns the summary buffer"
    (get-buffer-create (cedille-mode-get-summary-buffer-name))
)

(defun cedille-mode-get-summary-window()
  "Creates/gets and returns the summary window"
    (let ((summary-window (get-buffer-window (cedille-mode-get-summary-buffer))))
        (if summary-window
            summary-window
            (split-window)
        )
    )
)

(defun cedille-mode-summary-display()
  "Creates/destroys the summary window/buffer"
    (interactive)
    (let ((summary-buffer (cedille-mode-get-summary-buffer)))
        (if (get-buffer-window summary-buffer)
            (delete-window (cedille-mode-get-summary-window))
            (let* ((summary-pair (cedille-mode-get-all-summaries))
                    (summary-string (cedille-mode-summary-list-to-string (car summary-pair)))
                    (summary-starts (cdr summary-pair))
                    (main-buffer (current-buffer)))
                (set-window-buffer (cedille-mode-get-summary-window) summary-buffer)
                (with-current-buffer summary-buffer
                    (erase-buffer)
                    (insert summary-string)
                    (setq buffer-read-only t) 
                    ; variables set for use in summary minor mode
                    (setq cedille-mode-start-list summary-starts)
                    (make-local-variable 'cedille-mode-start-list)
                    (setq cedille-mode-main-buffer main-buffer)
                    (make-local-variable 'cedille-mode-main-buffer)
                    (cedille-summary-view-mode)
                )
            )
        )
    )
)

(provide 'cedille-mode-summary)
