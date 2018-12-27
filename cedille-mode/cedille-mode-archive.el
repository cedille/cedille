;;; cedille-mode-archive.el --- Archive a program to JSON and HTML

(require 'json)

(defun cedille-archive ()
  "Archive a program to JSON and HTML"
  (interactive)
  (if (eq major-mode 'cedille-mode)
      (cedille-save-archive)
    (user-error "Must be using cedille mode!")))

(defun cedille-save-archive ()
  (let ((archive-file-name (concat (buffer-name) ".html"))
	(text (buffer-substring-no-properties (point-min) (point-max)))
        (spans se-mode-spans))
    (with-temp-file archive-file-name
      (insert (cedille-spans-to-html spans text)))
    (message "Saved archive as %s" archive-file-name)))

(defun cedille-spans-to-json (spans)
  (json-encode (cedille-spans-to-sexp spans)))

(defun cedille-spans-to-sexp (spans)
  (mapcar 'cedille-span-to-sexp spans))

(defun cedille-span-to-sexp (span)
  `((name . ,(se-span-name span))
    (start . ,(se-span-start span))
    (end . ,(se-span-end span))
    (data . ,(se-span-data span))))

(defun cedille-spans-to-html (spans text)
  (let* ((header (format
		  "<script type=\"application/json\" id=\"spans\">%s</script><pre><code>"
		  (cedille-spans-to-json spans)))
	 (output (list header))
	 (index 1))
    (dolist (char (string-to-list text))
      (dotimes (_ (cl-count index spans :key 'se-span-end))
	(push "</span>" output))
      (dotimes (_ (cl-count index spans :key 'se-span-start))
	(push "<span>" output))
      (push (string char) output)
      (incf index))
    (push "</code></pre>" output)
    (apply 'concat (reverse output))))

(provide 'cedille-mode-archive)

;;; cedille-mode-archive.el ends here
