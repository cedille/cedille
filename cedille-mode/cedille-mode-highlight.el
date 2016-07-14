(require 'cedille-mode-faces)

(eval-when-compile (require 'cl))




(defgroup cedille-highlight nil
  "Syntax highlighting for Cedille."
  :group 'cedille)

(defcustom cedille-highlight-mode 'default
  "Highlighting scheme used in Cedille-mode buffers."
  :type '(choice
	  (const :tag "Default"        default)
	  (const :tag "Language Level" language-level)
	  (const :tag "Implicit Hidden" implicit-hidden)
	  )
  :group 'cedille-highlight)



(make-variable-buffer-local
 (defvar cedille-mode-highlight-face-map nil
   "Should be a mapping of qualities (strings) 
   to a mapping of values (strings) with faces (variables)"))



;; TODO: Check that MAP is appropriate
(defun set-cedille-mode-highlight-face-map (map)
  "Sets the  cedille-mode-highlight-face-map variable to MAP."
  (setq cedille-mode-highlight-face-map map))



(defun cedille-mode-highlight-default-old ()
  (interactive)
  "Sets the cedille-mode-highlight-face-map variable to 
   `cedille-mode-highlight-face-map-default' then highlights the file"
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-default-old)
  (cedille-mode-highlight-old))

(defun cedille-mode-highlight-language-level-old ()
  (interactive)
  "Sets the cedille-mode-highlight-face-map variable to 
   `cedille-mode-highlight-face-map-language-level' then highlights the file"
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-language-level-old)
  (cedille-mode-highlight-old))


(defun cedille-mode-highlight-implicit-hidden-old ()
 (interactive)
 "Sets the face to default but with implicit terms blended into the background."
 (set-face-attribute 'cedille-invisible-face-df nil :foreground
		      (face-attribute 'default :background))
 (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-implicit-hidden-old)
 (cedille-mode-highlight-old))


(defun cedille-mode-highlight-default ()
  (interactive)
  "Sets the cedille-mode-highlight-face-map variable to 
   `cedille-mode-highlight-face-map-default' then highlights the file"
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-default)
  (cedille-mode-highlight))

(defun cedille-mode-highlight-language-level ()
  (interactive)
  "Sets the cedille-mode-highlight-face-map variable to 
   `cedille-mode-highlight-face-map-language-level' then highlights the file"
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-language-level)
  (cedille-mode-highlight))



(defun cedille-mode-highlight ()
  "Highlights current buffer based on the
`ced-font-map'.  This will deactivate `font-lock-mode'."
  (when cedille-mode-highlight-face-map
    (let ((modified (buffer-modified-p))
	  (navi-on se-navigation-mode))
      (font-lock-mode -1)
      (mapcar 'cedille-mode-highlight-span (cdr cedille-mode-highlight-spans))
      (set-buffer-modified-p modified)
      (when navi-on
	(se-navigation-mode 1)))))

(defun cedille-mode-highlight-span (span)
  (let ((face (cedille-mode-highlight-get-face span cedille-mode-highlight-face-map))
	(start (se-span-start span))
	(end (se-span-end span)))
    (when face
      (put-text-property start end 'face face nil))))


(defun cedille-mode-highlight-get-face (span map)
  (if (equal map nil)
      nil
    (let* ((val (get-span-data-value span (caar map)))
	   (face (cdr (assoc  val (cdar map)))))
      (if face face
	(cedille-mode-highlight-get-face span (cdr map))))))


(defun get-span-data-value (span quality)
  (let ((data (se-span-data span)))
    (cond
     ((string= quality "name") (se-span-name span))
     ((string= quality "error") (if (cdr (assoc 'error data)) "error" nil)) 
     (t (cdr (assoc (intern quality) data))))))



(defun cedille-mode-highlight-old ()
  "Highlights current buffer based on the
`cedille-mode-highlight-face-map'.  This will deactivate `font-lock-mode'."
  (when cedille-mode-highlight-face-map
    (let ((modified (buffer-modified-p))
	  (navi-on se-navigation-mode))
      (font-lock-mode -1)
      (mapcar #'cedille-mode-highlight--term (cdr cedille-mode-highlight-spans))
      (set-buffer-modified-p modified)
      (when navi-on
	(se-navigation-mode 1))
      (font-lock-mode 1))))

(defun cedille-mode-highlight--term (term)
  (let ((name (se-term-name term))
	(start (se-term-start term))
	(end (se-term-end term))
	(face
	 (loop for (face . names) in cedille-mode-highlight-face-map
	       when (member (se-span-name term) names)
	       do (return face))))
    (when face
      (put-text-property start end 'face face nil))))


(provide 'cedille-mode-highlight)
