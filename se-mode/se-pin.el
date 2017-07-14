

(defvar se-pin-count 0
  "A number used as pins' IDs, so that we can match beginning pins with end pins. Every time a new pin is created, this variable is incremented by one.")

; Object returned by all "getter" functions
(defstruct
    (se-pin-item
     (:constructor new-pin-item (start end symbol id data)))
  start end symbol id data)

; Start is a boolean
(defstruct
    (se-pin-prop
     (:constructor new-pin-prop (symbol id start data)))
  symbol id start data)


;;;;; Public Functions ;;;;;

(defun se-pin-data (start end symbol data)
  "Pins data to the region between start and end in the current buffer"
  (setq end (- end 1))
  (setq id se-pin-count)
  (setq ps (new-pin-prop symbol id t data))
  (setq pe (new-pin-prop symbol id nil nil))
  (setq start-pins (get-text-property start 'se-pin))
  (setq end-pins (get-text-property end 'se-pin))
  (with-silent-modifications
    (if (equal start end)
	(put-text-property end (+ 1 end) 'se-pin (cons ps (cons pe end-pins))) ; Then
        (put-text-property start (+ 1 start) 'se-pin (cons ps start-pins)) ; Else...
        (put-text-property end (+ 1 end) 'se-pin (cons pe end-pins))))
  (incf se-pin-count))

(defun se-get-pins (symbol)
  "Gets all pins with symbol in the current buffer"
  (with-current-buffer (buffer-name) ; Makes sure that if the user switches buffer while this is running it won't cause any errors
    (reverse (se-get-pins-h symbol 1 '() (car (se-pin-get-starts-ends 1 symbol))))))

(defun se-pins-at (start end &optional symbol)
  "Gets the pins from start to end. If symbol is not nil, only pins with symbol are returned."
  (setq end (- end 1))
  (setq starts (car (se-pin-get-starts-ends start symbol)))
  (setq ends (cdr (se-pin-get-starts-ends end symbol)))
  (cdr (se-pin-get-pairs starts ends)))

(defun se-unpin (object &optional start end id)
  "Removes a pin. Object should either be a pin or a symbol (in which case start and end are required, but not id unless you want to only clear that specific id)."
  (with-silent-modifications
    (typecase object
      (se-pin-item
       (se-unpin (se-pin-item-symbol object) (se-pin-item-start object) (se-pin-item-end object) (se-pin-item-id object)))
      (t
       (setq end (- end 1))
       (put-text-property start (+ 1 start) 'se-pin (se-pins-without-symbol object start id))
       (put-text-property end (+ 1 end) 'se-pin (se-pins-without-symbol object end id))))))

(defun se-unpin-list (pins)
  "Unpins all in pins"
  (when pins
    (se-unpin (car pins))
    (se-unpin-list (cdr pins))))

(defun se-pin-clear-all (&optional symbol)
  "Clears all pins. If symbol is non-nil, this only removes pins with symbol."
  (if symbol
      (with-current-buffer (buffer-name) (se-pin-clear-all-h (se-get-pins symbol)))
      (put-text-property 1 (+ 1 (length (buffer-string))) 'se-pin nil))) ; Does (length (buffer-string)) need to have a + 1 on it to remove the property of the last character?



;;;;; Private Functions ;;;;;

(defun se-pin-clear-all-h (pins)
  "Helper for `se-pin-clear-all'"
  (when pins
    (se-unpin (car pins))
    (se-pin-clear-all-h (cdr pins))))

(defun se-pins-without-symbol (symbol pos &optional id)
  "Gets all pins without symbol and id from pin-list"
  (se-pins-without-symbol-h symbol id pos (get-text-property pos 'se-pin) '()))

(defun se-pins-without-symbol-h (symbol id pos pin-list new-list)
  "Helper for `se-pins-without-symbol'"
  (if (null pin-list)
      new-list
      (setq h (car pin-list))
      (unless (and (string= (symbol-name symbol) (symbol-name (se-pin-prop-symbol h))) (or (not id) (equal id (se-pin-prop-id h))))
	(setq new-list (cons h new-list)))
      (se-pins-without-symbol-h symbol id pos (cdr pin-list) new-list)))

(defun se-pin-remove-props (unused)
  "Removes all unused start and end pins"
  (when unused
    (let* ((h (car unused))
	   (prop (car h))
	   (pos (nth 1 h))
	   (symbol (se-pin-prop-symbol prop))
	   (id (se-pin-prop-id prop))
	   (new-props (se-pins-without-symbol symbol pos id)))
      (with-silent-modifications
	(put-text-property pos (+ 1 pos) 'se-pin new-props)))))

(defun se-get-pins-h (symbol pos pins starts)
  "Helper for `se-get-pins'"
  (setq next-change (next-single-property-change pos 'se-pin))
  (if (not next-change)
      (progn (se-pin-remove-props starts) pins)
      (when (get-text-property next-change 'se-pin)
	(setq starts-ends (se-pin-get-starts-ends next-change symbol))
	(setq starts (append starts (car starts-ends)))
	(setq ends (cdr starts-ends))
	(setq pin-pairs (se-pin-get-pairs starts ends))
	(setq starts (car pin-pairs))
	(setq pins (append (cdr pin-pairs) pins)))
      (se-get-pins-h symbol next-change pins starts)))

(defun se-pin-get-pairs (starts ends)
  "Pairs start and end pins"
  (se-pin-get-pairs-h starts ends '()))

(defun se-pin-get-pairs-h (starts ends pairs)
  "Helper for `se-pin-get-pairs'"
  (if (not (and starts ends))
      (cons starts pairs)
      (setq h (car ends))
      (setq pair (se-pin-get-pair starts h))
      (if (null (car pair))
	  (se-pin-remove-props (list h)) ; Then
	  (setq pairs (cons (car pair) pairs)) ; Else...
	  (setq starts (cdr pair)))
      (se-pin-get-pairs-h starts (cdr ends) pairs)))

(defun se-pin-get-pair (starts end)
  "Finds a pair for end in starts"
  (se-pin-get-pair-h starts end '()))

(defun se-pin-get-pair-h(starts end not-pairs)
  "Helper for `get-pin-pair'"
  (if starts
      (progn
	(setq h (car starts))
	(if (equal (se-pin-prop-id (car end)) (se-pin-prop-id (car h)))
	    (cons (new-pin-item (nth 1 h) (+ 1 (nth 1 end)) (se-pin-prop-symbol (car h)) (se-pin-prop-id (car h)) (se-pin-prop-data (car h))) (append not-pairs (cdr starts)))
	    (se-pin-get-pair-h (cdr starts) end (cons h not-pairs))))
      (cons nil not-pairs)))

(defun se-pin-get-starts-ends (pos &optional symbol)
  "Gets the start and end pins with symbol"
  (se-pin-get-starts-ends-h symbol (get-text-property pos 'se-pin) pos '() '()))

(defun se-pin-get-starts-ends-h (symbol pins pos starts ends)
  "Helper for `get-starts-ends'"
  (if (not pins)
      (cons starts ends)
      (setq h (car pins))
      (when (or (null symbol) (equal symbol (se-pin-prop-symbol h)))
	(setq h-pos (list h pos))
	(if (se-pin-prop-start h)
	    (se-pin-get-starts-ends-h symbol (cdr pins) pos (cons h-pos starts) ends)
	    (se-pin-get-starts-ends-h symbol (cdr pins) pos starts (cons h-pos ends))))))

(provide 'se-pin)
