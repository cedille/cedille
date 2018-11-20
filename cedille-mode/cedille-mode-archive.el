;;; cedille-mode-archive.el --- Archive a program to JSON and HTML

(require 'json)

(defun cedille-archive ()
  "Archive a program to JSON and HTML"
  (interactive)
  (if (eq major-mode 'cedille-mode)
      (cedille-save-archive)
    (user-error "Must be using cedille mode!")))

(defun cedille-save-archive ()
  (let ((archive-file-name (concat (buffer-name) ".json"))
        (spans se-mode-spans))
    (with-temp-file archive-file-name
      (insert (json-encode (cedille-spans-to-sexp spans))))
    (message "Saved archive as %s" archive-file-name)))

(defun cedille-spans-to-sexp (spans)
  (mapcar 'cedille-span-to-sexp spans))

(defun cedille-span-to-sexp (span)
  `((name . ,(se-span-name span))
    (start . ,(se-span-start span))
    (end . ,(se-span-end span))
    (data . ,(se-span-data span))))

(provide 'cedille-mode-archive)

;;; cedille-mode-archive.el ends here
