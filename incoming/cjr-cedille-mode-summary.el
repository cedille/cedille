;;; =====================================
;;; Implement top-level definitions view
;;; =====================================
;;;
;;;
;;;
;;; cedille-mode.el changes to make
;;;
;;; Load the file (somewhere past the navigation commands):
;;; (load "incoming/cjr-cedille-mode-summary")
;;;
;;; Add key to activate:
;;; (se-navi-define-key 'cedille-mode (kbd "S") #'cedille-mode-display-file-summary)
;;;


(defun cedille-mode-has-synthesized-type(data-list)
  "Return true/false if data portion of span has a synthesized-type portion"
    (if (assoc 'synthesized\ type data-list)
        t
        nil
    )
)
        
(defun cedille-mode-get-synthesized-type(data-list)
  "Return the synthesized type from the data portion of a span as a string"
    (cdr (assoc 'synthesized\ type data-list))
)

(defun cedille-mode-get-synthesized-signature-pair(span-string data-list)
  "Return the signature for a synthesized-type top-level definition"
    (cons (car (split-string span-string "=")) (cedille-mode-get-synthesized-type data-list))
)

(defun cedille-mode-get-rec-signature-pair(span-string)
  "Return the pair of the rec type name and the constructors"
    (let ((signature-pair (split-string (car (split-string span-string "=")) "\|")))
        (cons (substring (car signature-pair) 4 -2) (cdr signature-pair))
    )
)

(defun cedille-mode-get-signature-pair(span-string)
  "Return the pair of the definition name and type from the signature"
    (let ((signature-pair (split-string (car (split-string span-string "=")) "\u21D0")))
        (cons (car signature-pair) (cdr signature-pair))
    )
)

(defun cedille-mode-get-summary-pair(span)
  "Return the pair of name and type for a top-level definition"
    (let* ((span-string (buffer-substring (se-span-start span) (se-span-end span)))
         (first-string (car (split-string span-string " "))))
            ; check what the top-level definition is
            (cond   ((string= first-string "import") 
                        (cons span-string ""))
                    ((string= first-string "rec")
                        (cedille-mode-get-rec-signature-pair span-string))
                    (t ;default case
                        (if (cedille-mode-has-synthesized-type (se-span-data span))
                            ; synthesized type
                            (cedille-mode-get-synthesized-signature-pair span-string (se-span-data span))
                            ; non-synthesized type
                            (cedille-mode-get-signature-pair span-string)
                        ))
            )
    )
)

(defun cedille-mode-get-all-summary-pairs-helper(cur-top-level spans pair-list)
    (if spans
        ;step
        (if (se-term-child-p (car spans) cur-top-level)
            ;is child or equal
            (cedille-mode-get-all-summary-pairs-helper cur-top-level (cdr spans) pair-list)
            ;new top-level definition
            (cedille-mode-get-all-summary-pairs-helper (car spans) (cdr spans) 
                        (cons (cedille-mode-get-summary-pair (car spans)) pair-list))
        )
        ;base
        pair-list
    )
)

(defun cedille-mode-get-all-summary-pairs()
  "Return all of the summary pairs for the current spans"
    (interactive)
    (let ((spans (cdr se-mode-spans))) ;step past the cedille-file span
        (reverse (cedille-mode-get-all-summary-pairs-helper (car spans) (cdr spans) 
                    (cons (cedille-mode-get-summary-pair (car spans)) nil))
        )
    )
)

(defun cedille-mode-summary-list-to-string-helper(str)
  "Removes quotes and parenthesis from the lists converted to strings"
    (replace-regexp-in-string "\(" "" (
    replace-regexp-in-string "\)" "" (
    replace-regexp-in-string "\"" "" str)))
)

(defun cedille-mode-summary-list-to-string(pairs)
  "Convert the list of summary pairs to a single string"
    (if pairs
        ; need prin1-to-string function call or that argument fails a type-check during runtime
        (concat (substring (car (car pairs)) 0 -1) " : " 
                (cedille-mode-summary-list-to-string-helper(prin1-to-string (cdr (car pairs)))) "\n"
                    (cedille-mode-summary-list-to-string (cdr pairs)))
        ""
    )
)

(defun cedille-mode-display-file-summary()
  "Display a list of top level definitions (and types) in the info buffer"
    (interactive)
    (let ((summary-string (cedille-mode-summary-list-to-string (cedille-mode-get-all-summary-pairs))))
        (with-current-buffer (cedille-info-buffer)
            (erase-buffer)
            (insert summary-string)
            (setq buffer-read-only t)
        )
        (cedille-adjust-info-window-size)
    )
)

