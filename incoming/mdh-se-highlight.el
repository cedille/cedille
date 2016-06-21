



(eval-when-compile (require 'cl))




(make-variable-buffer-local
 (defvar se-highlight-font-map

   '(
    (se-default-face . ("Term variable" "Lambda abstraction (term-level)" "Lambda abstraction (type-level)" "Application of a term to a term" "Application of a type to a term" "Application of a type to a type" "Application of a term to a type" "Arrow type"))
    (se-red-face . ())
    (se-orange-face . ("Implicit dependent function type" "Erased lambda abstraction (term-level)"))
    (se-pink-face . ("Import of another source file""Constructor definition" "Recursive datatype definition" "Recursively defined type"))
    (se-purple-face . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon"))
    (se-blue-face . ("Type variable" "Dependent function type" "Implicit dependent function type" "Equation"))
    (se-green-face . ("Term-level definition (checking)" "Type-level definition (checking)"))
    (se-gray-face . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (se-warning-face . ())
    (se-error-face . ("Error" "hole" "Hole"))
    (se-highlighted-face . ())
    )
   
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
    (message name)
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



(defface se-orange-face
  '((t (:foreground "DarkOrange3")))
  "orange face")

(defface se-red-face
  '((t (:foreground "firebrick")))
  "red face")

(defface se-purple-face
  '((t (:foreground "purple")))
  "purple face")

(defface se-gray-face
  '((((background light))
     (:foreground "gray50"))
    (((background dark))
     (:foreground "gray75")))
  "gray face")
   
(defface se-blue-face
  '((t (:foreground "medium blue")))
  "blue face")

(defface se-green-face
  '((t (:foreground "green4")))
  "green face")

(defface se-pink-face
  '((t (:foreground "DeepPink2")))
  "pink face")

(defface se-default-face
  '((t nil))
  "default face")

(defface se-error-face
  '((t (:foreground "red" :underline t)))
  "error face, red with underline")

(defface se-warning-face
  '((t (:background "yellow"
		    :foreground "black")))
  "warning face, yellow highlight")

(defface se-highlighted-face
  '((t (:background "light blue"
		    :foreground "black")))
  "hightlighted-face, light blue highlight")




(provide 'se-highlight)
