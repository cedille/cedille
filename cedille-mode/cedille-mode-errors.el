(make-variable-buffer-local
 (defvar cedille-mode-error-spans nil
   "List of all error spans."))
 
;(make-variable-buffer-local
; (defvar cedille-mode-next-errors nil
;   "Next spans with an error value."))

(make-variable-buffer-local
 (defvar cedille-mode-cur-error nil
   "The currently selected error span."))

;(make-variable-buffer-local
; (defvar cedille-mode-prev-errors nil
;   "Previously seen spans with an error value."))

(defun cedille-span-has-error-data(data)
  "Return t if the span has error data, and nil otherwise."
  (assoc 'error data))

(defun cedille-find-error-spans(spans)
  "Sets `cedille-mode-error-spans' to hold a list
of spans that have an error value."
  (when spans
    (let ((cur (car spans)))
      (when (cedille-span-has-error-data (se-span-data cur))
	(push cur cedille-mode-error-spans))
      (cedille-find-error-spans (cdr spans)))))
    
(defun cedille-mode-set-error-spans()
  "After loading spans from the backend tool, this hook will look for error
spans and set the variable `cedille-mode-error-spans'.  The input is ignored."
  ;(setq cedille-mode-next-errors nil)
  ;(setq cedille-mode-prev-errors nil)
  (setq cedille-mode-cur-error nil)
  (setq cedille-mode-error-spans nil)
  (cedille-find-error-spans se-mode-spans)
  (setq cedille-mode-error-spans (reverse cedille-mode-error-spans)) ; we are pushing the errors as we find them, so the list is reversed
  )
  ;(setq cedille-mode-next-errors cedille-mode-error-spans))

(defun cedille-mode-any-errors()
  "Return t iff there are any errors."
  cedille-mode-error-spans)

(defun cedille-mode-select-span(cur)
  "Select and highlight the given span."
   (se-mode-update-selected (se-find-span-path cur (se-mode-parse-tree)))
   (se-mode-mark-term cur)
   (push (pop se-mode-not-selected) se-mode-selected)
   (cedille-mode-get-create-window (cedille-mode-inspect))
   (cedille-mode-update-buffers))
   ;;(display-buffer (cedille-mode-inspect)))

(defun cedille-mode-select-first-error(selected-span)  
  "Selects and highlights the first error in the selected span."
  (let ((first-error (car (delq nil (mapcar (lambda (x) (if (se-term-child-p x selected-span) x nil)) cedille-mode-error-spans)))))
    (if first-error
	(cedille-mode-select-error first-error)
        (message "No errors in selection")))) 

(defun cedille-mode-select-last-error(selected-span)  
  "Selects and highlight the last error in the selected span."
  (let ((last-error (last (delq nil (mapcar (lambda (x) (if (se-term-child-p x selected-span) x nil)) cedille-mode-error-spans)))))
    (if last-error
	(cedille-mode-select-error last-error)
        (message "No errors in selection"))))

(defun cedille-mode-select-error(error-span)
	"Select the given error span and update cur-error, next-errors, and prev-errors"
	(cedille-mode-select-span error-span)
	;(setq cedille-mode-next-errors (member error-span cedille-mode-error-spans))
	;(setq cedille-mode-prev-errors (reverse (butlast cedille-mode-error-spans (safe-length cedille-mode-next-errors))))
	(setq cedille-mode-cur-error error-span))

(defun cedille-mode-get-next-error(span next error-spans)
  "Gets the next error span after SPAN"
  (let ((h (car error-spans)))
    (if (null h)
	next
      (let ((ss (se-term-start span))
	    (se (se-term-end span))
	    (hs (se-term-start h))
	    (he (se-term-end h)))
      (if (and (not (and (equal ss hs) (equal se he))) (>= hs ss))
	  h
	(cedille-mode-get-next-error span next (cdr error-spans)))))))

(defun cedille-mode-get-prev-error(span prev error-spans)
  "Gets the next error span after SPAN"
  (let ((h (car error-spans)))
    (if (null h)
	prev
      (let ((ss (se-term-start span))
	    (se (se-term-end span))
	    (hs (se-term-start h))
	    (he (se-term-end h)))
      (if (and (not (and (equal ss hs) (equal se he))) (<= hs ss))
	  (cedille-mode-get-prev-error span h (cdr error-spans))
        prev)))))

(defun cedille-mode-next-error(count)
  "Select the next error from 'cedille-mode-next-errors', if any, and display the info buffer"
  (interactive "p")
  (if (<= count 0)
      (cedille-mode-highlight-occurrences-if)
    (if (se-mode-selected)
	(progn
	  (setq cedille-mode-cur-error (cedille-mode-get-next-error (se-mode-selected) nil cedille-mode-error-spans))
	  (if cedille-mode-cur-error
	      (cedille-mode-select-error cedille-mode-cur-error)
	    (if cedille-mode-wrap-navigation
		(cedille-mode-select-first-error-in-file)
	      (message "No further errors"))))
      (cedille-mode-select-first-error-in-file))
    (cedille-mode-next-error (- count 1))))
;    (if (null cedille-mode-next-errors)
;	(if (and (not (se-mode-selected)) cedille-mode-cur-error)
;	    (cedille-mode-select-span cedille-mode-cur-error)
;	  (if cedille-mode-wrap-navigation
;	      (cedille-mode-select-first-error-in-file)
;	    (message "No further errors")))
;      (cedille-mode-select-error (car cedille-mode-next-errors)))
;    (cedille-mode-next-error (- count 1))))

(defun cedille-mode-previous-error(count)
  "Select the previous error from 'cedille-mode-prev-erros', if any, and display the info buffer"
  (interactive "p")
  (if (<= count 0)
      (cedille-mode-highlight-occurrences-if)
    (if (se-mode-selected)
	(progn
	  (setq cedille-mode-cur-error (cedille-mode-get-prev-error (se-mode-selected) nil cedille-mode-error-spans))
	  (if cedille-mode-cur-error
	      (cedille-mode-select-error cedille-mode-cur-error)
	    (if cedille-mode-wrap-navigation
		(cedille-mode-select-last-error-in-file)
	      (message "No further errors"))))
      (when cedille-mode-wrap-navigation
	(cedille-mode-select-last-error-in-file)))
    (cedille-mode-previous-error (- count 1))))
;  (when (> count 0)
;    (if (null cedille-mode-prev-errors)
;	(if (and (not (se-mode-selected)) cedille-mode-cur-error)
;	    (cedille-mode-select-span cedille-mode-cur-error)
;	  (if cedille-mode-wrap-navigation
;	      (cedille-mode-select-last-error-in-file)
;	    (message "No previous errors")))
;      (cedille-mode-select-error (car cedille-mode-prev-errors)))
;    (cedille-mode-previous-error (- count 1))))


(defun cedille-mode-select-first-error-in-file()
  (interactive)
  (if (null cedille-mode-error-spans)
      (message "No errors.")
      (cedille-mode-select-error (car cedille-mode-error-spans))))

(defun cedille-mode-select-last-error-in-file()
  (interactive)
  (if (null cedille-mode-error-spans)
      (message "No errors.")
      (cedille-mode-select-error (last cedille-mode-error-spans))))

(defun cedille-mode-select-next-error(count)
  "Select the next error according to specifications, and display the info buffer."
  (interactive "p")
  (when (> count 0)
    (let ((selected-span nil));(if (se-mode-selected) (se-first-span (se-mode-selected)) nil)))
      (cond
        ; if there are no errors, say so
       ((null cedille-mode-error-spans) (message "No errors."))
        ; if nothing is selected, go to the next error
       ((null selected-span) (cedille-mode-next-error 1))
	; if the selected thing is the current error, go to the next error
       ((equal selected-span cedille-mode-cur-error) (cedille-mode-next-error 1))
        ; if the selected thing is another error, make it the current error
       ((member selected-span cedille-mode-error-spans) (cedille-mode-select-error selected-span))
        ; otherwise select the first error in the selected span 
       (t (cedille-mode-select-first-error selected-span))))
	(cedille-mode-select-next-error (- count 1))))

(defun cedille-mode-select-previous-error(count)
  "Select the previous error according to specifications, and display the info buffer."
  (interactive "p")
  (when (> count 0)
    (let ((selected-span nil));(if (se-mode-selected) (se-first-span (se-mode-selected)) nil)))
      (cond
        ; if there are no errors, say so
       ((null cedille-mode-error-spans) (message "No errors."))
        ; if nothing is selected, go to the previous error
       ((null selected-span) (cedille-mode-previous-error 1))
        ; if the selected thing is the current error, go to previous error
       ((equal selected-span cedille-mode-cur-error) (cedille-mode-previous-error 1))
        ; if the selected thing is another error, make it the current error
       ((member selected-span cedille-mode-error-spans) (cedille-mode-select-error selected-span))
        ; otherwise select the last error in the selected span
       (t (cedille-mode-select-last-error selected-span))))
    (cedille-mode-select-previous-error (- count 1))))


(provide 'cedille-mode-errors)
