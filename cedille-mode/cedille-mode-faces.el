

(defgroup cedille-highlight-faces-default nil
  "Faces used in Cedille's default highlighting mode."
  :group 'cedille-highlight)

(defgroup cedille-highlight-faces-language-level nil
  "Faces used in Cedille's langauge-level highlighting mode."
  :group 'cedille-highlight)


(defface cedille-error-face-df
  '((((background light))
     (:foreground "red" :underline t :weight bold))
    (((background dark))
     (:foreground "red1" :underline t :weight bold)))
  "The face used for errors."
  :group 'cedille-highlight-faces-default)

(defface cedille-hole-face-df
  '((((background light))
     (:foreground "black" :background "sky blue"))
    (((background dark))
     (:foreground "white" :background "sky blue")))
  "The face used for holes."
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
     (:foreground "red" :underline t :weight bold))
    (((background dark))
     (:foreground "brightred" :underline t :weight bold)))
  "The face used for errors."
  :group 'cedille-highlight-faces-language-level)

(defface cedille-hole-face-ll
  '((((background light))
     (:foreground "black" :background "sky blue"))
    (((background dark))
     (:foreground "white" :background "sky blue")))
  "The face used for holes."
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
  "The face used for non-language constructs."
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


(defface cedille-invisible-face-df
  '(( t (:foreground "black")))
  "The face set to background color to make terms disappear"
  :group 'cedille-highlight-faces-default)



(defvar cedille-mode-highlight-face-map-default-old

   '(
     (cedille-standard-face-df . ("Term variable" "Lambda abstraction (term-level)"
				  "Lambda abstraction (type-level)"
				  "Erased lambda abstraction (term-level)"
				  "Erased lambda abstraction (type-level)"))
    (cedille-comment-face-df . ())
    (cedille-keyword-face-df . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon" "Delta"
				"Import of another source file""Constructor definition"
				"Recursive datatype definition" "Recursively defined type"))
    (cedille-parentheses-face-df . ("Punctuation"))
    (cedille-type-face-df . ("Type variable" "Dependent function type"
		     "Implicit dependent function type" "Equation" "Arrow type"))
    (cedille-defined-face-df . ("Term-level definition (checking)"
		      "Type-level definition (checking)"))
    (cedille-kind-face-df . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (cedille-hole-face-df . ("Hole"))
    (cedille-error-face-df . ())
    )
   
   "Provides default highlighting scheme")

(defvar cedille-mode-highlight-face-map-language-level-old

   '(
     (cedille-term-face-ll . ("Term variable" "Lambda abstraction (term-level)"
			 "Lambda abstraction (type-level)"
			 "Term-level definition (checking)"
			 "Erased lambda abstraction (term-level)"))
    (cedille-comment-face-ll . ())
    (cedille-standard-face-ll . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon" "Delta"
				"Import of another source file" "Constructor definition"
				"Recursive datatype definition"))
    (cedille-parentheses-face-ll . ())
    (cedille-type-face-df . ("Type variable" "Dependent function type"
			     "Implicit dependent function type" "Equation" "Arrow type"
			     "Recursively defined type" "Type-level definition (checking)"
			     "Lambda abstraction (type-level)"
			     "Erased lambda abstraction (type-level)"))
    (cedille-kind-face-ll . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (cedille-hole-face-ll . ("Hole"))
    (cedille-error-face-ll . ())
    )
   
   "Provides language-level highlighting scheme")


(defvar cedille-mode-highlight-face-map-implicit-hidden-old

   '(
     (cedille-invisible-face-df . ("Erased lambda abstraction (term-level)"
				   "Erased lambda abstraction (type-level)"
				   "Implicit dependent function type"))
     (cedille-standard-face-df . ("Term variable" "Lambda abstraction (term-level)"
				  "Lambda abstraction (type-level)"))
    (cedille-comment-face-df . ())
    (cedille-keyword-face-df . ("Beta axiom" "Theta" "Rho" "Chi" "Epsilon" "Delta"
				"Import of another source file""Constructor definition"
				"Recursive datatype definition" "Recursively defined type"))
    (cedille-parentheses-face-df . ())
    (cedille-type-face-df . ("Type variable" "Dependent function type"
			     "Equation" "Arrow type"))
    (cedille-defined-face-df . ("Term-level definition (checking)"
		      "Type-level definition (checking)"))
    (cedille-kind-face-df . ("Star" "Pi kind" "Kind variable" "Arrow kind"))
    (cedille-hole-face-df . ("Hole"))
    (cedille-error-face-df . ())
    )
   
   "Provides default highlighting scheme while making implicit arguments invisible.")


;; '((quality . ((value . face)...))...)

;; quality           (list of values)
;;==============================================================================
;; language-level    (term type kind superkind)
;; name              ("[Level] variable" "[Level]-level definition (checking)"
;;                    "Application of a [level] to a [level]" "Arrow [level]"
;;                    "Implicit d/ Dependent function [level]"
;;                    "Erased l/ Lambda abstraction ([level]-level)"
;;                    "Beta Axiom" "Rho" Theta" "Chi" "Epsilon" "Delta"
;;                    "Recursive datatype definition" "Recursively defined type"
;;                    "Constructor definition"
;;                    "Star" "Pi [level]" "Equation" "Error" "Hole"
;;                    "Import of another source file" "Punctuation")
;; 'error
;;


(defvar cedille-mode-highlight-face-map-default
   '(
     ("name" . (("Hole" . cedille-hole-face-df)))
     ("error" . (("error" . cedille-error-face-df)))
     ("name" . (("Import of another source file" . cedille-keyword-face-df)
	       ("Constructor definition" . cedille-keyword-face-df)
	       ("Recursive datatype definition" . cedille-keyword-face-df)
	       ("Recursively defined type" . cedille-keyword-face-df)
	       ("Beta axiom" . cedille-keyword-face-df)
	       ("Rho" . cedille-keyword-face-df)
	       ("Theta" . cedille-keyword-face-df)
	       ("Epsilon" . ced-purple-face)
	       ("Chi" . cedille-keyword-face-df)
	       ("Term-level definition (checking)" . cedille-defined-face-df)
	       ("Type-level definition (checking)" . cedille-defined-face-df)
	       ("Kind-level definition (checking)" . cedille-defined-face-df)))	       
     ("language-level" . (("type" . cedille-type-face-df)
			 ("kind" . cedille-kind-face-df)
			 ("term" . cedille-standard-face-df)))
    )
   "Provides default highlighting scheme")



 (defvar cedille-mode-highlight-face-map-language-level
   '(
     ("name" . (("Hole" . cedille-hole-face-ll)))
     ("error" . (("error" . cedille-error-face-ll)))   
     ("language-level" . (("type" . cedille-type-face-ll)
			 ("kind" . cedille-kind-face-ll)
			 ("term" . cedille-term-face-ll)))
    )
   "Provides language-level highlighting scheme")



(provide 'cedille-mode-faces)
