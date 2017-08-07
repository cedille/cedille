;;;;; Markup code ;;;;;


(defun cedille-mode-markup-propertize-spans ()
  "Searches the parse tree for marked up text and converts it into pinned properties"
  (mapcar #'cedille-mode-markup-propertize-span se-mode-spans))


(defun cedille-mode-markup-propertize-span (span)
  "Converts marked up text into pinned properties"
  (setq fn (lambda (item)
	     (cond
	      ((and (sequencep item) (cdr item) (stringp (cdr item)))
	       (cons (car item) (cedille-mode-markup-propertize (cdr item))))
	      ((sequencep item) (mapcar fn item))
	      (t
	       (message "Remove the comment in cedille-mode-markup-propertize-span and this message line")
	       item)))) ; As of July 2017, this failsafe should never get called. However, I am including it in case some spans in the future are not one of the formats above. If the message shows up, delete the message line and this comment.
  (setf (se-span-data span) (mapcar fn (se-span-data span))))

(defun cedille-mode-markup-propertize (text)
  "Searches TEXT for markup stuff and turns it into pinned properties"
  (if (string= "" text)
      text
    (let ((split (cedille-mode-markup-split text)))
      (if (null split)
	  (concat (substring text 0 1) (cedille-mode-markup-propertize (substring text 1)))
	(let ((ep (nth 0 split))
	      (value (nth 1 split))
	      (name (nth 2 split))
	      (attrs (nth 3 split)))
	  (se-pin-data 0 (length value) (make-symbol name) attrs value)
	  (cedille-mode-markup-propertize (concat value (substring text ep))))))))

(defun cedille-mode-markup-split (text)
  (when (string= "<" (substring text 0 1))
    (setq space (string-match " " text 1)
	  close (string-match ">" text space))
    (when (and space close)
      (setq name (substring text 1 space)
	    attrs (cedille-mode-markup-split-h (concat (substring text (+ 1 space) close) " ") '() "")
	    end-tag (cedille-mode-markup-close-pos text (+ 1 close) 0 name))
      (when end-tag
	(setq value (substring text (+ 1 close) end-tag))
	(list (+ 3 end-tag (length name)) value name attrs)))))

(defun cedille-mode-markup-split-h (text attrs prev)
  "Helper for `cedille-mode-markup-split'"
  (if (string= "" text)
      (reverse attrs)
    (let ((h (substring text 0 1)))
      (if (string= " " h)
	  (let ((eq-pos (string-match "=" prev)))
	    (if (null eq-pos)
		(cedille-mode-markup-split-h (substring text 1) attrs (concat prev h))
	      (let ((name (substring prev 0 eq-pos))
		    (value (substring prev (+ eq-pos 1))))
		(cedille-mode-markup-split-h (substring text 1) (cons (cons name;(make-symbol name)
									    (cedille-mode-markup-remove-quotes value)) attrs) ""))))
	(cedille-mode-markup-split-h (substring text 1) attrs (concat prev h))))))

(defun cedille-mode-markup-remove-quotes (text)
  "Removes single quotes at the beginning and end of text"
  (unless (string= "" text)
    (when (string= "'" (substring text 0 1))
      (setq text (substring text 1)))
    (let ((len (length text)))
      (when (string= "'" (substring text (- len 1) len))
	(setq text (substring text 0 (- len 1))))))
  text)

(defun cedille-mode-markup-close-pos (text pos open attr)
  "Finds the position of the next closing </[ATTR]> in TEXT"
  (when (not (string= "" text))
    (cond
     ((string= "</" (substring text pos (+ pos 2)))
      (if (and (equal open 0) (string= attr (substring text (+ pos 2) (+ pos 2 (length attr)))))
	  pos
	(cedille-mode-markup-close-pos text (+ pos 1) (- open 1) attr)))
     ((string= "<" (substring text pos (+ pos 1)))
      (cedille-mode-markup-close-pos text (+ pos 1) (+ open 1) attr))
     (t (cedille-mode-markup-close-pos text (+ pos 1) open attr)))))


(provide 'cedille-mode-markup)
