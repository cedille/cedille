(require 'cedille-mode-faces)

(eval-when-compile (require 'cl))





(make-variable-buffer-local
 (defvar cedille-mode-highlight-font-map nil
   
   "Should be a mapping of faces or an abbreviated font-lock face
as symbols.

Example: 'function-name for `font-lock-function-name-face'

The cdr should be a list of se-span names that should have that
face.

Example: '(function-name . (\"defun\" \"defuns\"))"))



;; TODO: Check that MAP is appropriate
(defun set-cedille-mode-highlight-font-map (map)
  "Sets the  cedille-mode-highlight-fomt-map variable to MAP."
  (setq cedille-mode-highlight-font-map map))



(defun cedille-mode-highlight-default ()
  (interactive)
  "Sets the cedille-mode-highlight-font-map variable to 
   `cedille-mode-highlight-font-map-default' then highlights the file"
  (set-cedille-mode-highlight-font-map cedille-mode-highlight-font-map-default)
  (cedille-mode-highlight))

(defun cedille-mode-highlight-language-level ()
  (interactive)
  "Sets the cedille-mode-highlight-font-map variable to 
   `cedille-mode-highlight-font-map-language-level' then highlights the file"
  (set-cedille-mode-highlight-font-map cedille-mode-highlight-font-map-language-level)
  (cedille-mode-highlight))


(defun cedille-mode-highlight ()
  "Highlights current buffer based on the
`cedille-mode-highlight-font-map'.  This will deactivate `font-lock-mode'."
  (when cedille-mode-highlight-font-map
    (let ((modified (buffer-modified-p))
	  (navi-on se-navigation-mode))
      (font-lock-mode -1)
      (se-mapc #'cedille-mode-highlight--term se-mode-parse-tree)
      (set-buffer-modified-p modified)
      (when navi-on
	(se-navigation-mode 1))
      (font-lock-mode 1))))

(defun cedille-mode-highlight--term (term)
  (let ((name (se-term-name term))
	(start (se-term-start term))
	(end (se-term-end term))
	(face
	 (loop for (face . names) in cedille-mode-highlight-font-map
	       when (member (se-span-name term) names)
	       do (return face))))
    (message name)
    (when face
      (put-text-property start end 'face (cedille-mode-highlight-to-face face) nil))))

(defun cedille-mode-highlight-to-face (face)
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







(provide 'cedille-mode-highlight)
