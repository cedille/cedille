;;; cedille-mode-synthesis.el --- description -*- lexical-binding: t; -*-

;;; Code:

(require 'subr-x)

(defun get-span-type(data)
  "Filter out special attributes from the data in a span"
  (cdr (assoc 'expected-type data)))

(defun get-span-name(data)
  (cdr (assoc 'name data)))

(defun desambiguate-lambdas(term)
  (setq start 0)
  ;; make sure the hashtable will use string equality instead of object equality
  (setq vars-hash (make-hash-table :test 'equal))

  (while (string-match "λ \\([^\\.]*\\) \\." term start)
    (setq var (match-string 1 term))
    (setq varocc (gethash var vars-hash))
    (setq oldstart start)
    (setq start (match-end 0))
    (if (not varocc)
        (puthash var 1 vars-hash)
      (puthash var (1+ varocc) vars-hash)
      ;; FIXME: Use re to build this regexp interactively
      (setq newvar (concatenate 'string var (format "%d" varocc)))
      (setq rep0 (concatenate 'string "λ \\(" var))
      (setq rep (concatenate 'string rep0 "\\) .*"))
      (setq term (concat (substring term 0 oldstart)
                         (replace-regexp-in-string rep newvar term nil nil 1 oldstart)))
      ))
  term
  )

(defun synth-foralls(type)
  (replace-regexp-in-string "∀" "Λ" type)
  )

(defun synth-pis(type)
  (replace-regexp-in-string "Π" "λ" type)
  )

(defun synth-arrows(type)
  (while (string-match "^.*?\\([[:alnum:]]+? ➔\\)" type) ;; Create lambdas from arrows
    (setq s (downcase (match-string 1 type)))
    (setq s (substring s 0 1)) ;; Use the first letter of the type as the variable name
    ;; FIXME: Use re to build this regexp interactively
    (setq s (concatenate 'string "λ " s))
    (setq s (concatenate 'string s " ."))
    (setq type (replace-match s nil nil type 1))
    )
  (setq type (replace-regexp-in-string "\\.[^\\.]*$" ". " type)) ;; Delete the final return type
  )

(defun find-closing-parens(type start)
  (setq open_pars 1)
  (setq pos (1+ start)) ;; start right after the first parens
  (while (and (< pos (length type))(> open_pars 0))
    (setq c (aref type pos))
    (if (= c 40)
        (setq open_pars (1+ open_pars))
      (if (= c 41)
          (setq open_pars (1- open_pars))))
    (setq pos (1+ pos))

    )
  pos
  )

(defun find-first-parens(type)
  (string-match "\\((\\)" type)
  (match-beginning 1)
  )

;; This function is more complicated than simple regexes because
;; the balancing parenthesis problem is not a regular language
(defun synth-parens(type)
  (while (setq start (find-first-parens type))
    (setq end (find-closing-parens type start))
    (setq strhead (substring type 0 start))
    (setq strtail (substring type (+ 2 end)))
    (setq type (concatenate 'string strhead "λ f ."))
    (setq type (concatenate 'string type strtail))
    (string-match "" type) ;; clear the match for the next iteration
    )
  type
  )

(defun erase-types(type)
  (replace-regexp-in-string " : [^.]*" "" type)
  )

(defun synth-hole(type)
  (setq type (erase-types type))
  (setq type (synth-foralls type))
  (setq type (synth-pis type))
  (setq type (synth-parens type))
  (setq type (synth-arrows type))
  (desambiguate-lambdas type)
  )

(defun cedille-mode-synth-quantifiers ()
  "This function will synthesize the proper lambdas that match
the quantifiers at the given hole"
  (interactive)
  (if (null se-mode-selected)
      (message "Error: must select a node")
    (let* ((term (se-mode-selected))
           (d (se-term-to-json term))
           (name (se-term-name term))
           (type (get-span-type d))
           )
      (if (string= name 'Hole)
          (insert-before-markers (synth-hole type))
        (message "Synthesis can only be performed on a Hole")
        )
      )))

(provide 'cedille-mode-synthesis)
;;; cedille-mode-synthesis.el ends here
