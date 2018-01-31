;;;;; Markup code ;;;;;

(defun se-print-time (start &optional msg)
  (let* ((end (current-time))
         (high (- (nth 0 end) (nth 0 start)))
         (low (- (nth 1 end) (nth 1 start)))
         (micro (- (nth 2 end) (nth 2 start)))
         (pico (- (nth 3 end) (nth 3 start)))
	(time (time-to-seconds (list high low micro pico))))
    (message (or msg "time: %s") time)))

(defun se-markup-propertize-spans ()
  "Searches the parse tree for marked up text and converts it into pinned properties."
  ;(setq start (current-time))
  (mapcar #'se-markup-propertize-span se-mode-spans))
  ;(se-print-time start "markup time: %s"))


(defun se-markup-propertize-span (span)
  "Converts marked up text in SPAN's data into pinned properties"
  (setq fn (lambda (item)
	     (cond
	      ((and (sequencep item) (cdr item) (stringp (cdr item)))
	       (cons (car item) (se-markup-propertize (cdr item))))
	      ((sequencep item) (mapcar fn item))
	      ((stringp item) (se-markup-propertize item))
	      (t item))))
  (setf (se-span-data span) (mapcar fn (se-span-data span))))

(defun se-markup-propertize (text)
  "Searches TEXT for markup and turns it into pinned properties"
  (if (string= "" text)
      text
    (let ((split (se-markup-split text)))
      (if (null split)
	  (concat (substring text 0 1) (se-markup-propertize (substring text 1)))
	(let ((ep (nth 0 split))
	      (value (se-markup-propertize (nth 1 split)))
	      (name (nth 2 split))
	      (attrs (nth 3 split)))
	  (se-pin-data 0 (length value) (make-symbol name) attrs value)
	  (concat value (se-markup-propertize (substring text ep))))))))

(defun se-markup-split (text)
  (when (string= "<" (substring text 0 1))
    (setq space (string-match " " text 1)
	  close (string-match ">" text space))
    (when (and space close)
      (setq name (substring text 1 space)
	    attrs (se-markup-split-h (concat (substring text (+ 1 space) close) " ") '() "")
	    end-tag (se-markup-close-pos text (+ 1 close) 0 name))
      (when end-tag
	(setq value (substring text (+ 1 close) end-tag))
	(list (+ 3 end-tag (length name)) value name attrs)))))

(defun se-markup-split-h (text attrs prev)
  "Helper for `se-markup-split'"
  (if (string= "" text)
      (reverse attrs)
    (let ((h (substring text 0 1)))
      (if (string= " " h)
	  (let ((eq-pos (string-match "=" prev)))
	    (if (null eq-pos)
		(se-markup-split-h (substring text 1) attrs (concat prev h))
	      (let ((name (substring prev 0 eq-pos))
		    (value (substring prev (+ eq-pos 1))))
		(se-markup-split-h (substring text 1) (cons (cons name (se-markup-remove-quotes value)) attrs) ""))))
	(se-markup-split-h (substring text 1) attrs (concat prev h))))))

(defun se-markup-remove-quotes (text)
  "Removes curly single quotes at the beginning and end of text"
  (unless (string= "" text)
    (when (string= "‘" (substring text 0 1))
      (setq text (substring text 1)))
    (let ((len (length text)))
      (when (string= "’" (substring text (- len 1) len))
	(setq text (substring text 0 (- len 1))))))
  text)

(defun se-markup-close-pos (text pos open attr)
  "Finds the position of the next closing </[ATTR]> in TEXT"
  (when (not (string= "" text))
    (cond
     ((string= "</" (substring text pos (+ pos 2)))
      (if (and (equal open 0) (string= attr (substring text (+ pos 2) (+ pos 2 (length attr)))))
	  pos
	(se-markup-close-pos text (+ pos 1) (- open 1) attr)))
     ((string= "<" (substring text pos (+ pos 1)))
      (se-markup-close-pos text (+ pos 1) (+ open 1) attr))
     (t (se-markup-close-pos text (+ pos 1) open attr)))))

(provide 'se-markup)
