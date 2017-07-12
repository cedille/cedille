;(require 'cl)
;(require 'se-helpers)

(defvar se-pin-count 0
  "A number used as pins' IDs, so that we can match beginning pins with end pins. Every time a new pin is created, this variable is incremented by one.")

;(defvar se-pin-mode-clear 0 "Clear the pin")
;(defvar se-pin-mode-fixed 1 "Don't change the pin (if possible)")
;(defvar se-pin-mode-expand 2 "Expand the pin")
;(defvar se-pin-mode-shrink 3 "Shrink the pin")


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



;(defun se-pin-get-all-props ()
;  "Gets all pin properties"
;  (se-pin-get-all-props-h 1 '() (length (buffer-string))))

;(defun se-pin-get-all-props-h (pos props max-length)
;  "Helper for `se-pin-get-all-props'"
;  (if (equal pos max-length)
;      props
;      (setq pos-props (get-text-property pos 'se-pin))
;      (when pos-props
;	(setq props (append (list pos pos-props) props)))
;      (se-pin-get-all-props-h (+ 1 pos) props max-length)))



;;;;; Public Functions ;;;;;

(defun se-pin-data(start end symbol data); &optional mod-mode start-mode end-mode) ; expand-start and expand-end are bugged (don't use them)
  "Pins data to the region between start and end"
  (setq end (- end 1))

  ;(when (or (not mod-mode) (equal mod-mode se-pin-mode-fixed))
  ;  (setq mod-mode se-pin-mode-expand))
  ;(unless start-mode (setq start-mode se-pin-mode-fixed))
  ;(unless end-mode (setq end-mode se-pin-mode-fixed))
  
  (setq id se-pin-count)
  (setq ps (new-pin-prop symbol id t data))
  (setq pe (new-pin-prop symbol id nil nil))
  (setq start-pins (get-text-property start 'se-pin))
  (setq end-pins (get-text-property end 'se-pin))
  
  ;(setq remove-next-hook (se-curry #'se-pin-remove-next-hook symbol id))
  ;(setq replace-next-hook (se-curry #'se-pin-replace-next-hook symbol id))
  ;(setq replace-before-hook (se-curry #'se-pin-replace-before-hook symbol id))
  (setq remove-next-hook #'se-pin-remove-next-hook);(lambda (beg end) (se-pin-remove-next-hook symbol id beg end)))
  (setq replace-next-hook #'se-pin-replace-next-hook);(lambda (beg end) (se-pin-replace-next-hook symbol id beg end)))
  (setq replace-before-hook #'se-pin-replace-before-hook);(lambda (beg end) (se-pin-remove-before-hook symbol id data beg end)))

  (setq after-start-hooks (get-text-property start 'insert-in-front-hooks))
  (setq after-end-hooks (get-text-property end 'insert-in-front-hooks))
  (setq before-start-hooks (get-text-property start 'insert-behind-hooks))
  (setq before-end-hooks (get-text-property end 'insert-behind-hooks))

  ;(setq after-start-hooks (cons remove-next-hook after-start-hooks))
  ;(setq after-start-hooks (cons #'after-start-hook after-start-hooks))
  ;(setq after-end-hooks (cons #'after-end-hook after-end-hooks))
  ;(setq before-start-hooks (cons #'before-start-hook before-start-hooks))
  ;(setq before-end-hooks (cons #'before-end-hook before-end-hooks))
  ;(cond ((equal start-mode se-pin-mode-clear) ())
;	((equal start-mode sep-pin-mode-fixed) ())
;	((equal start-mode sep-pin-mode-expand) ())
;	((equal start-mode sep-pin-mode-shrink) ()))
 ; (cond ((equal end-mode se-pin-mode-clear) ())
;	((equal end-mode sep-pin-mode-fixed) ())
;	((equal end-mode sep-pin-mode-expand) ())
;	((equal end-mode sep-pin-mode-shrink) ()))
 ; (cond ((equal start-mode se-pin-mode-clear) ())
;	((equal start-mode sep-pin-mode-fixed) ())
;	((equal start-mode sep-pin-mode-expand) ())
;	((equal start-mode sep-pin-mode-shrink) ()))
  ;(when expand-start
  ;  (setq before-start-hooks (cons replace-before-hook before-start-hooks)))
  ;(when expand-end
  ;  (setq after-end-hooks (cons replace-next-hook after-end-hooks)))

  ;(message "with %s %s %s %s" after-start-hooks after-end-hooks before-start-hooks before-end-hooks)
  ;(message "se-pin-data %s %s" start end)
  (with-silent-modifications
    (if (equal start end)
	(put-text-property end (+ 1 end) 'se-pin (cons ps (cons pe end-pins))) ; Then
        (put-text-property start (+ 1 start) 'se-pin (cons ps start-pins)) ; Else...
        (put-text-property end (+ 1 end) 'se-pin (cons pe end-pins)))
        ;(put-text-property (+ 1 start) (+ 2 start) 'insert-in-front-hooks after-start-hooks)
        ;(put-text-property end (+ 1 end) 'insert-in-front-hooks after-end-hooks)
        ;(put-text-property (- start 1) (+ 1 start) 'insert-behind-hooks before-start-hooks)
        ;(put-text-property end (+ 1 end) 'insert-behind-hooks before-end-hooks))
    )
  (incf se-pin-count))

(defun se-pins-at (start end &optional symbol)
  "Gets the pins from start to end. If symbol is not nil, only pins with symbol are returned."
  (setq end (- end 1))
  (setq starts (car (get-starts-ends start symbol)))
  (setq ends (cdr (get-starts-ends end symbol)))
  (cdr (get-pin-pairs starts ends)))

(defun se-pin-exists-at (start end &optional symbol)
  "If a pin exists from start to end (with symbol if it is non-nil), it is returned; if a pin does not exist, nil is returned."
  ;(car (se-pins-at start end symbol)))
  (setq pins (se-pins-at start end symbol))
  (car pins))

(defun se-unpin (object &optional start end id)
  "Removes a pin. Object should either be a pin or a symbol (in which case start and end are required, but not id unless you want to only clear that specific id)."
  (with-silent-modifications
    (typecase object
      (se-pin-item
       (se-unpin (se-pin-item-symbol object) (se-pin-item-start object) (se-pin-item-end object) (se-pin-item-id object)))
      (t
       (setq end (- end 1))
       (put-text-property start (+ 1 start) 'se-pin (get-pins-without-symbol object start id))
       (put-text-property end (+ 1 end) 'se-pin (get-pins-without-symbol object end id))))))

(defun se-pin-clear-all (&optional symbol)
  "Clears all pins. If symbol is non-nil, this only removes pins with symbol."
  (if (null symbol)
      (put-text-property 1 (length (buffer-string)) 'se-pin nil)
      (se-pin-clear-all-h (se-get-pins symbol))))

(defun se-get-pins(symbol)
  "Gets all pins with symbol, starting at start (or beginning of buffer if start is nil)"
  (get-pins-h symbol 1 '() (car (get-starts-ends 1 symbol))))

(defun se-node-from(start end)
  "Finds a node that ranges from start to end in tree"
  (se-node-from-h start end (se-mode-parse-tree)))

(defun se-span-from(start end)
  "Finds a span that ranges from start to end in tree"
  (setq node (se-node-from start end))
  (when node (se-node-parent node)))
  


;;;;; Private Functions ;;;;;

(defun se-pin-clear-all-h (pins)
  "Helper for `se-pin-clear-all'"
  (when pins
    (se-unpin (car pins))
    (se-pin-clear-all-h (cdr pins))))


;(defun se-pin-remove-next-hook(beg end);symbol id beg end)
;  "Hook that removes the se-pin property from the next character when text is inserted after a character with an se-pin property"
;  (message "se-pin-remove-next-hook")); %s | %s | %s | %s" symbol id beg end))
;  ;(with-silent-modifications
;  ;  (put-text-property beg (+ 1 beg) 'se-pin (get-pins-without-symbol symbol id beg))))
;
;(defun se-pin-replace-next-hook(beg end);symbol id beg end)
;  "Hook that moves the se-pin property from one character to the next when text is inserted after a character with an se-pin property"
;  (message "se-pin-replace-next-hook")); %s | %s | %s | %s" symbol id beg end))
;  ;(setq pos (- beg 1))
;  ;(with-silent-modifications
;  ;  (put-text-property pos beg 'se-pin (get-pins-without-symbol symbol id pos))))
;
;(defun se-pin-replace-before-hook(beg end);symbol id data beg end)
;  "Hook that moves the se-pin property from one character to the next when text is inserted after a character with an se-pin property"
;  (message "se-pin-replace-before-hook")); %s | %s | %s | %s | %s" symbol id data beg end))
;  ;(setq pos (+ end 1))
;  ;(with-silent-modifications
;  ;  (put-text-property pos (+ 1 pos) 'se-pin (get-pins-without-symbol symbol id pos))
;  ;  (put-text-property beg (+ 1 beg) 'se-pin (new-pin-prop symbol id t data))))

(defun before-start-hook(symbol id start end)
  (message "before-start %s %s" start end))

(defun after-start-hook (start end)
  (message "after-start-hook %s %s" start end))

(defun before-end-hook (start end)
  (message "before-end-hook %s %s" start end))

(defun after-end-hook (start end)
  (message "after-end-hook %s %s" start end))

(defun get-pins-without-symbol (symbol pos &optional id)
  "Gets all pins without symbol and id from pin-list"
  (get-pins-without-symbol-h symbol id pos (get-text-property pos 'se-pin) '()))

(defun get-pins-without-symbol-h (symbol id pos pin-list new-list)
  "Helper for `get-pins-without-symbol'"
  (if (null pin-list)
      new-list
      (setq h (car pin-list))
      (unless (and (string= (symbol-name symbol) (symbol-name (se-pin-prop-symbol h))) (or (not id) (equal id (se-pin-prop-id h))))
	(setq new-list (cons h new-list)))
      (get-pins-without-symbol-h symbol id pos (cdr pin-list) new-list)))

(defun se-pin-remove-props (unused)
  "Removes all unused start and end pins"
  ;(message "se-pin-remove-props %s" unused)
  (when unused
    (let* ((h (car unused))
	   (prop (car h))
	   (pos (nth 1 h))
	   (symbol (se-pin-prop-symbol prop))
	   (id (se-pin-prop-id prop))
	   (new-props (get-pins-without-symbol symbol pos id)))
      (with-silent-modifications
	(put-text-property pos (+ 1 pos) 'se-pin new-props)))))

(defun get-pins-h (symbol pos pins starts)
  "Helper for `se-get-pins'"
  (setq next-change (next-single-property-change pos 'se-pin))
  (if (not next-change)
      (progn 
	(se-pin-remove-props starts)
	;(message "not next-change %s" starts)
	pins)
      (when (get-text-property next-change 'se-pin)
	(setq starts-ends (get-starts-ends next-change symbol))
	(setq starts (append starts (car starts-ends)))
	(setq ends (cdr starts-ends))
	(setq pin-pairs (get-pin-pairs starts ends))
	(setq starts (car pin-pairs))
	(setq pins (append (cdr pin-pairs) pins)))
      (get-pins-h symbol next-change pins starts)))

(defun get-pin-pairs (starts ends)
  "Pairs start and end pins"
  (get-pin-pairs-h starts ends '()))

(defun get-pin-pairs-h (starts ends pairs)
  "Helper for `get-pin-pairs'"
  (if (not (and starts ends)) ; Here (both)
      (cons starts pairs)
      (setq h (car ends))
      (setq pair (get-pin-pair starts h))
      (if (null (car pair))
	  ;(let* ((prop (car h)) ; Then
	;	 (end (nth 1 h))
	;	 (symbol (se-pin-prop-symbol prop))
	;	 (id (se-pin-prop-id prop))
	;	 (new-props (get-pins-without-symbol symbol end id)))
	    ;(put-text-property end (+ 1 end) 'se-pin new-props))
	  (se-pin-remove-props (list h)) ; Then
	  ;;(setq unused-ends (cons h unused-ends)) ; Then
	  (setq pairs (cons (car pair) pairs)) ; Else...
	  ;(message "cdr pair = %s" (cdr pair))
	  (setq starts (cdr pair)))
      (get-pin-pairs-h starts (cdr ends) pairs)))

(defun get-pin-pair (starts end)
  "Finds a pair for end in starts"
  (get-pin-pair-h starts end '()))

(defun get-pin-pair-h(starts end not-pairs)
  "Helper for `get-pin-pair'"
  (if starts ; Here
      (progn
	(setq h (car starts))
	(if (equal (se-pin-prop-id (car end)) (se-pin-prop-id (car h)))
	    (cons (new-pin-item (nth 1 h) (+ 1 (nth 1 end)) (se-pin-prop-symbol (car h)) (se-pin-prop-id (car h)) (se-pin-prop-data (car h))) (append not-pairs (cdr starts)))
	    (get-pin-pair-h (cdr starts) end (cons h not-pairs))))
      (cons nil not-pairs)))

(defun get-starts-ends (pos &optional symbol)
  "Gets the start and end pins with symbol"
  (get-starts-ends-h symbol (get-text-property pos 'se-pin) pos '() '()))

(defun get-starts-ends-h(symbol pins pos starts ends)
  "Helper for `get-starts-ends'"
  (if (not pins) ; Here
      (cons starts ends)
      (setq h (car pins))
      (when (or (null symbol) (equal symbol (se-pin-prop-symbol h)))
	(setq h-pos (list h pos))
	(if (se-pin-prop-start h)
	    (get-starts-ends-h symbol (cdr pins) pos (cons h-pos starts) ends)
	    (get-starts-ends-h symbol (cdr pins) pos starts (cons h-pos ends))))))


(defun se-node-from-h(start end tree)
  "Helper for `se-node-from'"
  (typecase tree
    (se-node
     (setq parent (se-node-parent tree))
     (if (and (eq start (se-span-start parent)) (eq end (se-span-end parent)))
	 tree
         (se-map-1 (se-curry #'se-node-from-h start end) (se-node-children tree))))
    (sequence
     (se-map-1 (se-curry #'se-node-from-h start end) tree))))



(provide 'se-pin)
