;;; cedille-mode-synthesis.el --- description -*- lexical-binding: t; -*-

;;; Code:

(defun get-span-type(data)
  "Filter out special attributes from the data in a span"
  (cdr (assoc 'expected-type data)))

(defun get-span-name(data)
  (cdr (assoc 'name data)))

(defun cedille-mode-synth-quantifiers ()
  "This function will syntehsize the proper lambdas that match
the quantifiers at the given hole"
  (interactive)
  (when se-mode-selected
    (let* (
           (term (se-mode-selected))
           (d (se-term-to-json term))
           (name (se-term-name term))
           (type (get-span-type d))
           )
      (when (string= name 'Hole)
        (insert type))
      )))

(provide 'cedille-mode-synthesis)
;;; cedille-mode-synthesis.el ends here
