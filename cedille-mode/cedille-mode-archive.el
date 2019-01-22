;;; cedille-mode-archive.el --- Archive a program to JSON and HTML

(require 'json)

(defun cedille-archive-read-file (filename)
  "Read one of the template files for the archiving (to html) feature"
   (with-temp-buffer
     (insert-file-contents (concat cedille-path-el "cedille-mode/" filename))
     (buffer-string)))

(defconst cedille-archive-html-template
  (cedille-archive-read-file "cedille-mode-archive-template.html"))

(defconst cedille-archive-javascript
  (cedille-archive-read-file "cedille-mode-archive.js"))

(defun cedille-archive ()
  "Archive a program to JSON and HTML"
  (interactive)
  (if (eq major-mode 'cedille-mode)
      (cedille-save-archive)
    (user-error "Must be using cedille mode!")))

(defun cedille-save-archive ()
  (let ((buffer-name (buffer-name))
        (archive-file-name (concat (buffer-name) ".html"))
        (text (buffer-substring-no-properties (point-min) (point-max)))
        (spans se-mode-spans))
    (with-temp-file archive-file-name
      (insert (format cedille-archive-html-template
                      (cedille-buffer-to-json buffer-name spans text)
                      cedille-archive-javascript)))
    (message "Saved archive as %s" archive-file-name)))

(defun cedille-buffer-to-json (buffer-name spans text)
  (json-encode
   `((,buffer-name . ((text . ,text)
                      (spans . ,(cedille-spans-to-sexp spans)))))))

(defun cedille-spans-to-sexp (spans)
  (mapcar 'cedille-span-to-sexp spans))

(defun cedille-span-to-sexp (span)
  `((name . ,(se-span-name span))
    (start . ,(se-span-start span))
    (end . ,(se-span-end span))
    (data . ,(se-span-data span))))

(provide 'cedille-mode-archive)

;;; cedille-mode-archive.el ends here
