;;; cedille-mode-synthesis.el --- description -*- lexical-binding: t; -*-

;;; Code:

(require 'subr-x)

(defun get-span-typeorkind(data)
  "Filter out special attributes from the data in a span"
  (or (cdr (assoc 'expected-type data))
           (cdr (assoc 'expected-kind data)))
  )

(defun get-span-name(data)
  (cdr (assoc 'name data)))

(defun desambiguate-lambdas(term)
  (setq start 0)
  ;; make sure the hashtable will use string equality instead of object equality
  (setq vars-hash (make-hash-table :test 'equal))

  (while (string-match "λ \\([^\\.]+?\\) \\." term start)
    (setq var (match-string 1 term))
    (setq varocc (gethash var vars-hash))
    (if (not varocc)
        (puthash var 1 vars-hash)
      (puthash var (1+ varocc) vars-hash)
      (setq newvar (concatenate 'string var (format "%d" varocc)))
      (setq rep (format "λ \\(%s\\).*" var))
      (setq term (concat (substring term 0 start)
                         (replace-regexp-in-string rep newvar term nil nil 1 start)))
      )
    (setq start (match-end 0)))
  term
  )


(defun synth-foralls(type)
  (replace-regexp-in-string "∀" "Λ" type t)
  )

(defun synth-pis(type)
  (replace-regexp-in-string "Π" "λ" type t)
  )

(defun synth-arrows(type lamb arrow)
  (setq rep (format "[\\^\\.➾➔]?[ ]?\\(\\([^\\.➾➔]*\\) %s\\)" arrow))
  (while (string-match rep type)
    ;; string= messes up the match data, so we have to restore it before doing the replacement
    (setq data (match-data))
    (setq s (downcase (match-string 2 type)))

    ;; Use the first letter of the type as the variable name
    (unless (string= s "eq")
        (setq s (substring s 0 1))) ;; But maintain if it's eq

    (if (string= s "★")
        (setq s "K"))
    (setq newtxt (format "%s %s ." lamb s))
    (set-match-data data)
    (setq type (replace-match newtxt t nil type 1))
    )
  type
  )

(defun delete-return-type(type)
  (replace-regexp-in-string "\\.[^\\.]*$" ". " type)
  )

(defun find-closing-delim(type start delim-open delim-close)
  (setq open_delims_count 1)
  (setq ch_close (aref delim-close 0))
  (setq ch_open (aref delim-open 0))
  (setq pos (1+ start)) ;; start right after the first delim
  (while (and (< pos (length type))(> open_delims_count 0))
    (setq c (aref type pos))
    (if (= c ch_open)
        (setq open_delims_count (1+ open_delims_count))
      (if (= c ch_close)
          (setq open_delims_count (1- open_delims_count))))
    (setq pos (1+ pos)) )
  pos
  )

;; This function is more complicated than simple regexes because
;; the balancing parenthesis problem is not a regular language
(defun synth-func(type delim-open delim-close var)
  (while (setq start (string-match (format "\\(%s\\)" delim-open) type)) ;; Finds first bracket
    (setq end (find-closing-delim type start delim-open delim-close))
    (setq strhead (substring type 0 start))
    (setq strtail (substring type end))
    (setq type (format "%s%s%s" strhead var strtail))
    )
  type
  )


(defun erase-types(type)
  (replace-regexp-in-string ": [^.]*" "" type)
  )

(defun erase-iotas(type)
  (replace-regexp-in-string "ι[^.]*?. " "" type)
  )

(defun synth-parens(type)
  (synth-func type "(" ")" "f")
  )

(defun synth-eqs(type)
  (synth-func type "{" "}" "eq")
  )

(defun synth-regular-arrows(type)
  (synth-arrows type "λ" "➔")
  )

(defun synth-erased-arrows(type)
  (synth-arrows type "Λ" "➾")
  )

(defun synth-hole(type)
  (setq type (erase-types type))
  (setq type (erase-iotas type))
  (setq type (synth-foralls type))
  (setq type (synth-pis type))
  (setq type (synth-parens type))
  (setq type (synth-eqs type))
  (setq type (synth-regular-arrows type))
  (setq type (synth-erased-arrows type))
  (setq type (delete-return-type type))
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
           (type (get-span-typeorkind d))
           )
      (if (string= name 'Hole)
          (insert-before-markers (synth-hole type))
        (message "Synthesis can only be performed on a Hole")
        )
      )))

(provide 'cedille-mode-synthesis)
;;; cedille-mode-synthesis.el ends here
