

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

(defun se-pin-data (start end symbol data &optional object)
  "Pins DATA to the region between START and END in OBJECT (can be a buffer, a string, or nil, in which case it defaults to the current buffer)"
  (let* ((end (- end 1))
	 (id se-pin-count)
	 (ps (new-pin-prop symbol id t data))
	 (pe (new-pin-prop symbol id nil nil))
	 (start-pins (get-text-property start 'se-pin object))
	 (end-pins (get-text-property end 'se-pin object)))
    (with-silent-modifications
      (if (equal start end)
	  (put-text-property end (+ 1 end) 'se-pin (cons ps (cons pe end-pins)) object)
        (put-text-property start (+ 1 start) 'se-pin (cons ps start-pins) object)
        (put-text-property end (+ 1 end) 'se-pin (cons pe end-pins) object))))
  (incf se-pin-count)
  object)

(defun se-print-prop-str (str)
  "Prints STR in a way that show its properties"
  (if (string= "" str)
      ""
    (let* ((prop-str (format "%s" (text-properties-at 0 str))))
      (concat "\n\t" (substring str 0 1) ": " prop-str (se-print-prop-str (substring str 1))))))

(defun se-get-pins (symbol &optional object start end)
  "Gets all pins with symbol in OBJECT (can be a string or a buffer) from START to END (if nil, START defaults to the start of OBJECT, and END to the end of OBJECT)"
  (with-current-buffer (if (and object (bufferp object)) object (buffer-name))
      (let ((start (or start (if (se-pin-bufferp object) 1 0))))
	(reverse (se-get-pins-h-h symbol start end '() '() object)))))

(defun se-pins-at (start end &optional symbol object)
  "Gets the pins exactly from start to end. If SYMBOL is not nil, only pins with SYMBOL are returned. OBJECT can be a string or a buffer (or nil, defaulting to the current buffer)."
  (let ((n (if (se-pin-bufferp object) 1 0))
	(end (- end 1)))
    (when (and (<= start end) (>= start n) (>= end n))
      (let ((starts (car (se-pin-get-starts-ends start symbol object)))
	    (ends (cdr (se-pin-get-starts-ends end symbol object))))
        (cdr (se-pin-get-pairs starts ends object t))))))

(defun se-unpin (object &optional start end id string-or-buffer)
  "Removes a pin. OBJECT should either be a pin or a symbol (in which case start and end are required, but not ID unless you want to only clear that specific id). STRING-OR-BUFFER should, as the name implies, be nil (defaulting to the current buffer), a string, or a buffer ;)."
  (with-silent-modifications
    (typecase object
      (se-pin-item
       (se-unpin (se-pin-item-symbol object) (se-pin-item-start object) (se-pin-item-end object) (se-pin-item-id object) string-or-buffer))
      (t
       (let ((end (- end 1)))
         (put-text-property start (+ 1 start) 'se-pin (se-pins-without-symbol object start id string-or-buffer) string-or-buffer)
         (put-text-property end (+ 1 end) 'se-pin (se-pins-without-symbol object end id string-or-buffer) string-or-buffer))))))

(defun se-unpin-list (pins &optional object)
  "Unpins all in PINS. OBJECT should be a string or a buffer (or nil, which defaults to the current buffer)"
  (when pins
    (se-unpin (car pins) nil nil nil object)
    (se-unpin-list (cdr pins) object)))

(defun se-pin-clear-all (&optional symbol object)
  "Clears all pins. If SYMBOL is non-nil, this only removes pins with SYMBOL. OBJECT should be nil (defaulting to the current buffer), a string, or a buffer."
  (if symbol
      (se-pin-clear-all-h (se-get-pins symbol) object)
    (if (and object (stringp object))
	(put-text-property 0 (length object) 'se-pin nil object)
      (put-text-property 1 (+ 1 (buffer-size)) 'se-pin nil object))))



;;;;; Private Functions ;;;;;

(defun se-pin-bufferp (object)
  (or (null object) (bufferp object)))

(defun se-pin-to-string (object)
  "Makes sure that object is a string. If it is nil, it uses the current buffer's text. If it is a buffer, it uses that text."
  (cond
   ((null object) (buffer-string))
   ((get-buffer object) (with-current-buffer object (buffer-string)))
   ((stringp object) object)))

(defun se-pin-clear-all-h (pins object)
  "Helper for `se-pin-clear-all'"
  (when pins
    (se-unpin (car pins) nil nil nil object)
    (se-pin-clear-all-h (cdr pins) object)))

(defun se-pins-without-symbol (symbol pos &optional id object)
  "Gets all pins without symbol and id from pin-list"
  (se-pins-without-symbol-h symbol id pos (get-text-property pos 'se-pin object) '() object))

(defun se-pins-without-symbol-h (symbol id pos pin-list new-list object)
  "Helper for `se-pins-without-symbol'"
  (if (null pin-list)
      new-list
    (let ((h (car pin-list))
          (new-list new-list))
      (unless (and (string= symbol (se-pin-prop-symbol h)) (or (not id) (equal id (se-pin-prop-id h))))
        (setq new-list (cons h new-list)))
      (se-pins-without-symbol-h symbol id pos (cdr pin-list) new-list object))))

(defun se-pin-remove-props (unused &optional object)
  "Removes all unused start and end pins"
  (when unused
    (let* ((h (car unused))
	   (prop (car h))
	   (pos (nth 1 h))
	   (symbol (se-pin-prop-symbol prop))
	   (id (se-pin-prop-id prop))
	   (new-props (se-pins-without-symbol symbol pos id object)))
      (with-silent-modifications
	(put-text-property pos (+ 1 pos) 'se-pin new-props object))
      (se-pin-remove-props (cdr unused) object))))

(defun se-get-pins-h (symbol pos end pins starts object)
  "Helper for `se-get-pins'"
  (se-get-pins-h-h symbol (next-single-property-change pos 'se-pin object end) end pins starts object))

(defun se-get-pins-h-h (symbol pos end pins starts object)
  "Helper for `se-get-pins-h'"
  (if (or (not pos) (equal pos end))
      (progn (se-pin-remove-props starts object) pins)
    (if (get-text-property pos 'se-pin object)
        (let* ((starts-ends (se-pin-get-starts-ends pos symbol object))
               (starts (append starts (car starts-ends)))
               (ends (cdr starts-ends))
               (pin-pairs (se-pin-get-pairs starts ends object))
               (starts (car pin-pairs))
               (pins (append (cdr pin-pairs) pins)))
          (se-get-pins-h symbol pos end pins starts object))
      (se-get-pins-h symbol pos end pins starts object))))

(defun se-pin-get-pairs (starts ends object &optional no-remove)
  "Pairs start and end pins"
  (se-pin-get-pairs-h starts ends '() object no-remove))

(defun se-pin-get-pairs-h (starts ends pairs object no-remove)
  "Helper for `se-pin-get-pairs'"
  (if (not (and starts ends))
      (cons starts pairs)
      (let* ((h (car ends))
             (pair (se-pin-get-pair starts h)))
        (if (null (car pair))
            (unless no-remove (se-pin-remove-props (list h)))
          (setq pairs (cons (car pair) pairs)
                starts (cdr pair)))
        (se-pin-get-pairs-h starts (cdr ends) pairs object no-remove))))

(defun se-pin-get-pair (starts end)
  "Finds a pair for end in starts"
  (se-pin-get-pair-h starts end '()))

(defun se-pin-get-pair-h(starts end not-pairs)
  "Helper for `get-pin-pair'"
  (if (null starts)
      (cons nil not-pairs)
    (let ((h (car starts)))
      (if (equal (se-pin-prop-id (car end)) (se-pin-prop-id (car h)))
          (cons (new-pin-item (nth 1 h) (+ 1 (nth 1 end)) (se-pin-prop-symbol (car h)) (se-pin-prop-id (car h)) (se-pin-prop-data (car h))) (append not-pairs (cdr starts)))
        (se-pin-get-pair-h (cdr starts) end (cons h not-pairs))))))

(defun se-pin-get-starts-ends (pos &optional symbol object)
  "Gets the start and end pins with symbol"
  (se-pin-get-starts-ends-h symbol (get-text-property pos 'se-pin object) pos '() '()))

(defun se-pin-get-starts-ends-h (symbol pins pos starts ends)
  "Helper for `get-starts-ends'"
  (if (not pins)
      (cons starts ends)
    (let ((h (car pins))
          (starts starts)
          (ends ends))
      (when (or (null symbol) (string= symbol (se-pin-prop-symbol h)))
        (let ((h-pos (list h pos)))
          (if (se-pin-prop-start h)
              (setq starts (cons h-pos starts))
            (setq ends (cons h-pos ends)))))
      (se-pin-get-starts-ends-h symbol (cdr pins) pos starts ends))))

(provide 'se-pin)
