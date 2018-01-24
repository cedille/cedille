;(require 'cedille-mode-faces)

(eval-when-compile (require 'cl))


(defgroup cedille-highlight nil
  "Syntax highlighting for Cedille."
  :group 'cedille)

(defcustom cedille-highlight-mode 'default
  "Highlighting scheme used in Cedille-mode buffers."
  :type '(choice
	  (const :tag "Default"          default)
	  (const :tag "Language Level"   language-level)
	  (const :tag "Checking Mode"    checking-mode)
	  (const :tag "Implicit Hidden"  implicit-hidden)
	  )
  :group 'cedille-highlight)


(make-variable-buffer-local
 (defvar cedille-mode-highlight-spans nil
   "A list of spans to highlight"))


(make-variable-buffer-local
 (defvar cedille-mode-highlight-face-map nil
   "Should be a mapping of qualities (strings) 
   to a mapping of values (strings) with faces (variables)"))



;; TODO: Check that MAP is appropriate
(defun set-cedille-mode-highlight-face-map (map)
  "Sets the  cedille-mode-highlight-face-map variable to MAP."
  (setq cedille-mode-highlight-face-map map))




;; Interactive Calls -------------------------------------------------------


(defun cedille-mode-highlight-default ()
  "Sets the cedille-mode-highlight-face-map variable to 
   `cedille-mode-highlight-face-map-default' then highlights the file"
  (interactive)
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-default)
  (cedille-mode-highlight))

(defun cedille-mode-highlight-language-level ()
  "Sets the cedille-mode-highlight-face-map variable to 
   `cedille-mode-highlight-face-map-language-level' then highlights the file"
  (interactive)
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-language-level)
  (cedille-mode-highlight))

(defun cedille-mode-highlight-checking-mode ()
  "Sets the cedille-mode-highlight-face-map variable to
   `cedille-mode-highlight-face-map-checking-mode' then highlights the file"
  (interactive)
  (set-cedille-mode-highlight-face-map cedille-mode-highlight-face-map-checking-mode)
  (cedille-mode-highlight))


;; Highlighting code -----------------------------------------------------

(defun cedille-mode-highlight ()
  "Highlights current buffer based on the
`ced-font-map'.  This will deactivate `font-lock-mode'."
  (with-silent-modifications ; If you apply a text property, it exits se-navigation-mode (and, consequently, cedille navi mode). Using `with-silent-modifications', you can make changes to the buffer without alerting it of the changes.
    (when cedille-mode-highlight-face-map
      (font-lock-mode -1)
      (mapcar 'cedille-mode-highlight-span (cdr cedille-mode-highlight-spans))
      (cedille-mode-update-overlays))))

(defun cedille-mode-update-overlays ()
  "Updates error and hole overlays."
  (with-silent-modifications
    (remove-overlays (point-min) (point-max) 'help-echo "error")
    (remove-overlays (point-min) (point-max) 'help-echo "hole")
    (overlay-recenter (point-max))
    (cedille-mode-highlight-error-overlay cedille-mode-error-spans)))
    ;(cedille-mode-highlight-hole-overlay cedille-mode-error-spans)))


(defun cedille-mode-highlight-span (span)
  (let ((face (cedille-mode-highlight-get-face span cedille-mode-highlight-face-map))
	(start (se-span-start span))
	(end (se-span-end span)))
    (when face
      (with-silent-modifications
	(put-text-property start end 'face face nil)))))

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
     ;; ((string= quality "error") (if (cdr (assoc 'error data)) "error" nil)) 
     (t (cdr (assoc (intern quality) data))))))

(defun cedille-mode-highlight-shadowed ()
  "Searches for 'shadowed'-attribute markup in STR and highlights them"
  (let* ((fn (lambda (pins)
               (when pins
                 (let* ((h (car pins))
                        (s (se-pin-item-start h))
                        (e (se-pin-item-end h)))
                   (put-text-property s e 'face `(:foreground ,cedille-mode-context-shadowed-color))
                 (funcall fn (cdr pins)))))))
    (funcall fn (se-get-pins 'shadowed))))


(provide 'cedille-mode-highlight)
