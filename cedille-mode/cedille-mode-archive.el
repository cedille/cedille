;; -*- lexical-binding: t -*-
;;; cedille-mode-archive.el --- Archive a program to JSON and HTML

(require 'json)

(defun cedille-mode-archive-read-file (filename)
  "Read one of the template files for the archiving (to html) feature"
  (with-temp-buffer
    (insert-file-contents (concat cedille-path-el "cedille-mode/" filename))
    (buffer-string)))

(defconst cedille-mode-archive-html-template
  (cedille-mode-archive-read-file "cedille-mode-archive-template.html"))

(defconst cedille-mode-archive-javascript
  (cedille-mode-archive-read-file "cedille-mode-archive.js"))

(defun cedille-mode-archive ()
  (interactive)
  (unless (eq major-mode 'cedille-mode)
    (user-error "Must be using cedille mode!"))
  (run-with-timer 1 nil
                  'cedille-mode-archive-timer
                  (buffer-name)
                  (buffer-file-name)))

(defun cedille-mode-archive-timer (buffer-name buffer-file-name)
  (with-current-buffer buffer-name
    (when cedille-mode-caching
      (user-error "Must wait for caching to finish!"))
    (se-inf-interactive
     (cedille-mode-concat-sep "archive" buffer-file-name)
     (lambda (archive extra)
       (let ((archive-file-name (concat buffer-name ".html")))
         (with-temp-file archive-file-name
           (insert (format cedille-mode-archive-html-template
                           archive
                           cedille-mode-archive-javascript)))
         (message "Saved archive as %s" archive-file-name)))
     nil
     :header "Archiving")))

(provide 'cedille-mode-archive)

;;; cedille-mode-archive.el ends here
