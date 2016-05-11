
;; Code inspired by Agda2-mode's goals.

(defvar se-hole-open-delimiter "{"
  "Characters to show as the opening of a hole.")

(defvar se-hole-close-delimiter " }"
  "Characters to show as the ending of a hole.")

(defvar se-hole-syntax '("{!" . "!}")
  "Pair of strings to mark beginning and end of holes.  These
will be hidden and the user will see `se-hole-open-delimiter' and
`se-hole-close-delimiter' instead.")

(defvar se-hole-hook nil
  "Function hooks to be called when a hole is created.  Four
arguments are given as points: INNER-START INNER-END
DELIMITER-START DELIMITER-END.  Be sure to include undo
information if necessary.")

(defun se-hole-insert (point)
  "Inserts hole at POINT."
  (interactive "d")
  (se-hole-create point point ""))

(defun se-hole-match (start end)
  "Match existing hole from `se-hole-syntax' in region and setup
text properties."
  (interactive "r")
  (let ((inner-start (se-hole-match-open-delimiter  start end))
	(inner-end   (se-hole-match-close-delimiter start end)))
    (unless (and inner-start inner-end)
      (error "Could not match hole"))
    (let ((outer-start (se-hole--open-delimiter-start inner-start))
	  (outer-end   (se-hole--close-delimiter-end  inner-end)))
      (se-hole--set-text-props inner-start inner-end)
      (se-hole--push-undo-props outer-start inner-start)
      (se-hole--push-undo-props inner-end   outer-end)
      (run-hook-with-args 'se-hole-hook
			  inner-start inner-end
			  outer-start outer-end))))

(defun se-hole-create (start &optional end replace)
  "Insert a hole at position START.  Inserts hole over region if
END is non-nil.  Region is placed into hole unless REPLACE is
non-nil.  If REPLACE is a string it will be used as replacement
text."
  (interactive "r")
  (cond
   ((null start)
    (error "Could not create hole"))
   ((null end)
    (se-hole-create start start replace))
   ((stringp replace)
    ;; replace region, setup hole
    (delete-region start end)
    (insert (car se-hole-syntax)
	    replace
	    (cdr se-hole-syntax))
    (se-hole-match start (point)))
   ((null replace)
    ;; keep region, setup hole
    (se-hole-create start end (buffer-substring start end)))
   (replace
    ;; destroy region, setup hole
    (se-hole-create start end ""))))

(defun se-hole-remove-props (start end)
  "Will indiscriminately remove properties set by `se-hole-create'."
  (interactive "r")
  (let ((inhibit-modification-hooks t))
    (remove-text-properties start end (list 'display nil
					    'rear-nonsticy nil
					    'modification-hooks nil))))

(defun se-hole-match-open-delimiter (start end)
  "Matches end of starting delimiter of `se-hole-syntax' in
region.  Returns nil if not matched."
  (save-excursion
    (goto-char start)
    (search-forward (car se-hole-syntax) end t nil)))

(defun se-hole-match-close-delimiter (start end)
  "Matches start of ending delimiter of `se-hole-syntax' in
region.  Returns nil if not matched."
  (save-excursion
    (goto-char end)
    (search-backward (cdr se-hole-syntax) start t nil)))

(defun se-hole--push-undo-props (start end)
  (push `(apply se-hole-remove-props ,start ,end)
	buffer-undo-list))

(defun se-hole--set-text-props (start end)
  (add-text-properties (se-hole--open-delimiter-start start) start
		       (list 'display se-hole-open-delimiter
			     'rear-nonsticky t
			     'modification-hooks '(se-hole--signal-read-only)))
  (add-text-properties (se-hole--close-delimiter-end end) end
		       (list 'display se-hole-close-delimiter
			     'rear-nonsticky t
			     'modification-hooks '(se-hole--signal-read-only))))

(defun se-hole--signal-read-only (&rest beg end args)
  (signal 'text-read-only nil))

(defun se-hole--open-delimiter-start (end)
  (- end (length (car se-hole-syntax))))

(defun se-hole--close-delimiter-end (start)
  (+ start (length (cdr se-hole-syntax))))

(provide 'se-hole)
