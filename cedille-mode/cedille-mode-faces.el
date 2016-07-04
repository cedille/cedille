

(make-variable-buffer-local
 (defvar cedille-mode-highlight-font-map-default

   '(
     (cedille-default-face . ("Term variable" "Lambda abstraction (term-level)"
			 "Lambda abstraction (type-level)" "Application of a term to a term"
			 "Application of a type to a term" "Application of a type to a type"
			 "Application of a term to a type" "Arrow type"))
    (cedille-red-face . ())
    (cedille-orange-face . ("Implicit dependent function type"
		       "Erased lambda abstraction (term-level)"))
    (cedille-pink-face . ("Import of another source file""Constructor definition"
		     "Recursive datatype definition" "Recursively defined type"))
    (cedille-purple-face . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon"))
    (cedille-blue-face . ("Type variable" "Dependent function type"
		     "Implicit dependent function type" "Equation"))
    (cedille-green-face . ("Term-level definition (checking)"
		      "Type-level definition (checking)"))
    (cedille-gray-face . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (cedille-warning-face . ())
    (cedille-error-face . ("Error" "hole" "Hole"))
    (cedille-highlighted-face . ())
    )
   
   "Provides default highlighting scheme"))





(defface cedille-orange-face
  '((t (:foreground "DarkOrange3")))
  "orange face")

(defface cedille-red-face
  '((t (:foreground "firebrick")))
  "red face")

(defface cedille-purple-face
  '((t (:foreground "purple")))
  "purple face")

(defface cedille-gray-face
  '((((background light))
     (:foreground "gray50"))
    (((background dark))
     (:foreground "gray75")))
  "gray face")

(defface cedille-blue-face
  '((t (:foreground "medium blue")))
  "blue face")

(defface cedille-green-face
  '((t (:foreground "green4")))
  "green face")

(defface cedille-pink-face
  '((t (:foreground "DeepPink2")))
  "pink face")

(defface cedille-default-face
  '((t nil))
  "default face")

(defface cedille-error-face
  '((t (:foreground "red" :underline t)))
  "error face, red with underline")

(defface cedille-warning-face
  '((t (:background "yellow"
		    :foreground "black")))
  "warning face, yellow highlight")

(defface cedille-highlighted-face
  '((t (:background "light blue"
		    :foreground "black")))
  "hightlighted-face, light blue highlight")

(provide 'cedille-mode-faces)
