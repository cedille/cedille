

;;;;;;;; Starting code ;;;;;;;;
(defun cedille-mode-br-start ()
  "Opens the beta-reduction buffer with the selected span"
  (interactive)
  (let ((sel (se-mode-selected)))
    (if sel
	(cedille-mode-br-span sel)
      (call-interactively #'cedille-mode-br-prompt))))

(defun cedille-mode-br-span (span)
  "Starts beta-reduction buffer with span"
  ; Do something here
)

(defun cedille-mode-br-request-text (span)
  "Gets the text to send to the backend as a request to beta-reduce a span")

(defun cedille-mode-br-prompt (input)
  "Starts beta-reduction buffer with the prompted input INPUT"
  (interactive "MBeta-reduce: ")
  ; Do something here
)



(provide 'cedille-mode-beta-reduce)
