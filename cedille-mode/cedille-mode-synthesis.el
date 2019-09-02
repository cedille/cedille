;;; cedille-mode-synthesis.el --- description -*- lexical-binding: t; -*-

;;; Code:

(require 'subr-x)

;; This function was taken as is from
;; https://emacs.stackexchange.com/questions/33892/replace-element-of-alist-using-equal-even-if-key-does-not-exist/33893#33893
(defun alist-set (key val alist &optional symbol)
  "Set property KEY to VAL in ALIST. Return new alist.
This creates the association if it is missing, and otherwise sets
the cdr of the first matching association in the list. It does
not create duplicate associations. By default, key comparison is
done with `equal'. However, if SYMBOL is non-nil, then `eq' is
used instead.

This method may mutate the original alist, but you still need to
use the return value of this method instead of the original
alist, to ensure correct results."
  (if-let ((pair (if symbol (assq key alist) (assoc key alist))))
      (setcdr pair val)
    (push (cons key val) alist))
  alist)

(defun get-span-type(data)
  "Filter out special attributes from the data in a span"
  (cdr (assoc 'expected-type data)))

(defun get-span-name(data)
  (cdr (assoc 'name data)))

(defun desambiguate-lambdas(term)
  (setq vars nil)
  (setq start 0)
  (while (string-match "λ \\(.*\\) : .* \\." term start)
    (setq start (match-end 0))
    (setq var (match-string 1 term))
    (if (assoc var vars)
        (progn ;; if branch
          (setq occs (assoc var vars))
          (alist-set var (+1 occs) vars) ;; update the value of key=var
          )
      (cons '(var . 0) vars) ;; else branch
      )
    )
  )

(defun synth-hole(type)
  (setq type (replace-regexp-in-string "∀" "Λ" type)) ;; Replace foralls
  (setq type (replace-regexp-in-string "Π" "λ" type)) ;; Replace Pis
  (while (string-match "\\. \\([^\\.➔]*\\) ➔" type) ;; Create lambdas from arrows
    (setq s (downcase (match-string 1 type)))
    (setq s (concatenate 'string ". λ " s))
    (setq s (concatenate 'string s " : \\1 ."))
    (setq type (replace-match s nil nil type))
    )
  (replace-regexp-in-string "\\.[^\\.]*$" ". " type) ;; Delete the final return type
  ;; (desambiguate-lambdas type)
  )

(defun cedille-mode-synth-quantifiers ()
  "This function will synthesize the proper lambdas that match
the quantifiers at the given hole"
  (interactive)
  (when se-mode-selected
    (let* ((term (se-mode-selected))
           (d (se-term-to-json term))
           (name (se-term-name term))
           (type (get-span-type d))
           (synth-type (synth-hole type))
           )
      (when (string= name 'Hole)
        (insert-before-markers synth-type))
      )))

(provide 'cedille-mode-synthesis)
;;; cedille-mode-synthesis.el ends here
