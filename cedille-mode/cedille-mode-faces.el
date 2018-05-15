


(defgroup cedille-highlight-faces-default nil
  "Faces used in Cedille's default highlighting mode."
  :group 'cedille-highlight)

(defgroup cedille-highlight-faces-language-level nil
  "Faces used in Cedille's langauge-level highlighting mode."
  :group 'cedille-highlight)

(defgroup cedille-highlight-faces-checking-mode nil
  "Faces used in Cedille's checking-mode highlighting mode."
  :group 'cedille-highlight)

;; ----------------------------------------------------------
;; default faces
;; ----------------------------------------------------------

(defface cedille-error-face-df	       
   '((((background light))
      (:foreground unspecified :underline t :weight bold :slant italic))
     (((background dark))
      (:foreground unspecified :underline t :weight bold :slant italic)))
   "The face used for errors."
   :group 'cedille-highlight-faces-default)

(defface ced-purple-face
  '((((background light))
     (:foreground "purple"))
    (((background dark))
     (:foreground "purple")))
    "The face used for Epsilon spans"
    :group 'cedille-highlight-faces-default)


(defface cedille-standard-face-df
  '((t nil))
  "The default/standard face."
  :group 'cedille-highlight-faces-default)

(defface cedille-ignore-face-df
  '((t (:foreground unspecified :background unspecified)))
  "The face that leaves the previously-highlighted face alone.")

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

(defface cedille-invisible-face-df
  '(( t (:foreground "black")))
  "The face set to background color to make terms disappear"
  :group 'cedille-highlight-faces-default)


;; -----------------------------------------------------
;; language-level faces
;; -----------------------------------------------------


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


;; ------------------------------------------------------
;; checking-mode faces
;; ------------------------------------------------------


(defface cedille-checking-face-cm
  '((((background light))
     (:foreground "medium blue"))
    (((background dark))
     (:foreground "sky blue")))
  "The face used for checking mode."
  :group 'cedille-highlight-faces-checking-mode)



(defface cedille-synthesizing-face-cm
  '((((background light))
     (:foreground "firebrick" ))
    (((background dark))
     (:foreground "red")))
  "The face used for synthesizing mode."
  :group 'cedille-highlight-faces-checking-mode)


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
     ("name" . (("Import of another source file" . cedille-keyword-face-df)
               ("Module header" . cedille-keyword-face-df)
               ("Module declaration" . cedille-kind-face-df)
               ("Imported module" . cedille-kind-face-df)
	       ("Constructor definition" . cedille-keyword-face-df)
	       ("Recursive datatype definition" . cedille-keyword-face-df)
	       ("Recursively defined type" . cedille-keyword-face-df)
	       ("Beta axiom" . cedille-keyword-face-df)
	       ("Rho" . cedille-keyword-face-df)
               ("Phi" . cedille-keyword-face-df)
	       ("Theta" . cedille-keyword-face-df)
	       ("Epsilon" . ced-purple-face)
	       ("Chi" . cedille-keyword-face-df)
               ("Delta" . cedille-keyword-face-df)
	       ("Comment" . cedille-comment-face-df)
	       ("Whitespace" . cedille-standard-face-df)
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
     ("language-level" . (("type" . cedille-type-face-ll)
			 ("kind" . cedille-kind-face-ll)
			 ("term" . cedille-term-face-ll)))
    )
   "Provides language-level highlighting scheme")

(defvar cedille-mode-highlight-face-map-checking-mode
  '(
    ("punctuation" . (("true" . cedille-ignore-face-df)))
    ("checking-mode" . (("checking" . cedille-checking-face-cm)
		       ("synthesizing" . cedille-synthesizing-face-cm)))
    )
  "Provides checking-mode highlighting scheme")



;; -------------------------------------------------------------------
;; Error Overlay
;; -------------------------------------------------------------------


(defun cedille-mode-highlight-error-overlay (spans)
  (when (car spans)
    (if (string= (se-span-name (car spans)) "Hole")
	(let ((over (make-overlay (se-span-start (car spans))
				  (se-span-end (car spans))
				  nil nil 1)))
	  (overlay-put over 'face 'cedille-hole-face-df)
	  (overlay-put over 'evaporate 1)
	  (overlay-put over 'help-echo "hole"))
      (let ((over (make-overlay (se-span-start (car spans))
				(se-span-end (car spans))
				nil nil 1)))
	(overlay-put over 'face 'cedille-error-face-df)
	(overlay-put over 'evaporate 1)
	(overlay-put over 'help-echo "error")))
    (cedille-mode-highlight-error-overlay (cdr spans))))


;; -----------------------------------------------------------------
;; Hole Overlay
;; -----------------------------------------------------------------
    
   
(defun cedille-mode-highlight-hole-overlay (spans)
  (when (car spans)
    (when (string= (se-span-name (car spans)) "Hole")
      (let ((over (make-overlay (se-span-start (car spans))
				(se-span-end (car spans))
				nil nil 1)))
	(overlay-put over 'face 'cedille-hole-face-df)
	(overlay-put over 'evaporate 1)
	(overlay-put over 'help-echo "hole")))
    (cedille-mode-highlight-hole-overlay (cdr spans))))


(provide 'cedille-mode-faces)
