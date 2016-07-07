
(defgroup cedille nil
  "Need a catch-all for Cedille options; move this to cedille-mode later."
  :group 'langauges)

(defgroup cedille-highlight nil
  "Syntax highlighting for Cedille."
  :group 'cedille)

(defcustom cedille-highlight-mode 'non-interactive
  "Highlighting scheme used in Cedille-mode buffers."
  :type '(choice
	  (const :tag "Default"        default)
	  (const :tag "Language-level" language-level)
	  )
  :group 'cedille-highlight
)

(defgroup cedille-highlight-faces-default nil
  "Faces used in Cedille's default highlighting mode."
  :group 'cedille-highlight)

(defgroup cedille-highlight-faces-language-level nil
  "Faces used in Cedille's langauge-level highlighting mode."
  :group 'cedille-highlight)



(defface cedille-error-face-df
  '((((background light))
     (:foreground "red" :underline t))
    (((background dark))
     (:foreground "red1" :underline t)))
  "The face used for errors and holes."
  :group 'cedille-highlight-faces-default)


(defface cedille-comment-face-df
  '((((background light))
     (:foreground "firebrick"))
    (((background dark))
     (:foreground "firebrick")))
  "The face used for comments."
  :group 'cedille-highlight-faces-default)


(defface cedille-keyword-face-df
  '((((background light))
     (:foreground "DarkOrange3"))
    (((background dark))
     (:foreground "orange")))
  "The face used for keywords."
  :group 'cedille-highlight-faces-default)

(defface cedille-defined-face-df
  '((((background light))
     (:foreground "green4"))
    (((background dark))
     (:foreground "darkgreen")))
  "The face used for user-defined symbols."
  :group 'cedille-highlight-faces-default)

(defface cedille-parentheses-face-df
  '((((background light))
     (:foreground "DeepPink2"))
    (((background dark))
     (:foreground "magenta")))
  "The face used for parentheses."
  :group 'cedille-highlight-faces-default)

(defface cedille-standard-face-df
  '((t nil))
  "The default/standard face."
  :group 'cedille-highlight-faces-default)

(defface cedille-type-face-df
  '((((background light))
     (:foreground "MediumBlue"))
    (((background dark))
     (:foreground "DeepSkyBlue")))
  "The face used for types."
  :group 'cedille-highlight-faces-default)

(defface cedille-kind-face-df
  '((((background light))
     (:foreground "DarkViolet"))
    (((background dark))
     (:foreground "purple")))
  "The face used for kinds."
  :group 'cedille-highlight-faces-default)

(defface cedille-error-face-ll
  '((((background light))
     (:foreground "red" :underline t))
    (((background dark))
     (:foreground "brightred" :underline t)))
  "The face used for errors and holes."
  :group 'cedille-highlight-faces-language-level)

(defface cedille-comment-face-ll
  '((((background light))
     (:foreground "firebrick"))
    (((background dark))
     (:foreground "firebrick")))
  "The face used for comments."
  :group 'cedille-highlight-faces-language-level)

(defface cedille-standard-face-ll
  '((t nil))
  "The face used for terms."
  :group 'cedille-highlight-faces-language-level)

(defface cedille-term-face-ll
  '((((background light))
     (:foreground "green3"))
    (((background dark))
     (:foreground "SpringGreen")))
  "The face used for terms."
  :group 'cedille-highlight-faces-language-level)

(defface cedille-type-face-ll
  '((((background light))
     (:foreground "MediumBlue"))
    (((background dark))
     (:foreground "DeepSkyBlue")))
  "The face used for types."
  :group 'cedille-highlight-faces-language-level)

(defface cedille-kind-face-ll
  '((((background light))
     (:foreground "DarkMagenta"))
    (((background dark))
     (:foreground "magenta")))
  "The face used for kinds."
  :group 'cedille-highlight-faces-language-level)


(defface cedille-parentheses-face-ll
  '((((background light))
     (:foreground "DarkOrange3"))
    (((background dark))
     (:foreground "orange")))
  "The face used for parentheses."
  :group 'cedille-highlight-faces-language-level)






(defvar cedille-mode-highlight-font-map-default

   '(
     (cedille-standard-face-df . ("Term variable" "Lambda abstraction (term-level)"
				  "Lambda abstraction (type-level)"
				  "Erased lambda abstraction (term-level)"
				  "Erased lambda abstraction (type-level)"))
    (cedille-comment-face-df . ())
    (cedille-keyword-face-df . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon"
				"Import of another source file""Constructor definition"
				"Recursive datatype definition" "Recursively defined type"))
    (cedille-parentheses-face-df . ())
    (cedille-type-face-df . ("Type variable" "Dependent function type"
		     "Implicit dependent function type" "Equation" "Arrow type"))
    (cedille-defined-face-df . ("Term-level definition (checking)"
		      "Type-level definition (checking)"))
    (cedille-kind-face-df . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (cedille-error-face-df . ("Hole"))
    )
   
   "Provides default highlighting scheme")

(defvar cedille-mode-highlight-font-map-language-level

   '(
     (cedille-term-face-ll . ("Term variable" "Lambda abstraction (term-level)"
			 "Lambda abstraction (type-level)"
			 "Term-level definition (checking)"
			 "Erased lambda abstraction (term-level)"))
    (cedille-comment-face-ll . ())
    (cedille-standard-face-ll . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon"
				"Import of another source file" "Constructor definition"
				"Recursive datatype definition"))
    (cedille-parentheses-face-ll . ())
    (cedille-type-face-df . ("Type variable" "Dependent function type"
			     "Implicit dependent function type" "Equation" "Arrow type"
			     "Recursively defined type" "Type-level definition (checking)"
			     "Lambda abstraction (type-level)"
			     "Erased lambda abstraction (type-level)"))
    (cedille-kind-face-ll . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (cedille-error-face-ll . ("Hole"))
    )
   
   "Provides language-level highlighting scheme")



(provide 'cedille-mode-faces)
