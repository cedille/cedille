
(eval-when-compile (require 'cl))

(make-variable-buffer-local
 (defvar se-highlight-font-map nil
   "Should be a mapping of faces or an abbreviated font-lock face
as symbols.

Example: 'function-name for `font-lock-function-name-face'

The cdr should be a list of se-span names that should have that
face.

Example: '(function-name . (\"defun\" \"defuns\"))"))

(defun se-highlight ()
  "Highlights current buffer based on the
`se-highlight-font-map'.  This will deactivate `font-lock-mode'."
  (interactive)
  (when se-highlight-font-map
    (let ((modified (buffer-modified-p))
	  (navi-on se-navigation-mode))
      (font-lock-mode -1)
      (se-mapc #'se-highlight--term se-mode-parse-tree)
      (set-buffer-modified-p modified)
      (when navi-on
	(se-navigation-mode 1)))))

(defun se-highlight--term (term)
  (let ((name (se-term-name term))
	(start (se-term-start term))
	(end (se-term-end term))
	(face
	 (loop for (face . names) in se-highlight-font-map
	       when (member (se-span-name term) names)
	       do (return face))))
    (when face
      (put-text-property start end 'face (se-highlight-to-face face) nil))))

(defun se-highlight-to-face (face)
  "Returns font lock face symbol abbreviated by FACE if exists,
otherwise returns FACE."
  (let ((orig face))
    (when (symbolp face)
      (setq face (symbol-name face)))
    (if (not (stringp face))
	orig
      (setq face (intern (concat "font-lock-" face "-face")))
      (if (and (boundp face)
	       (symbol-value face))
	  face orig))))

(provide 'se-highlight)
