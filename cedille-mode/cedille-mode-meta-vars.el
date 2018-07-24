

(defstruct meta-var name kind type)

(defvar cedille-mode-meta-vars-list nil
  "List of meta-var structs")


(defun cedille-mode-meta-var-solved(mv)
  (meta-var-type mv))


(defun cedille-mode-compute-meta-vars()
  "Computes the meta-variables at the current node"
  nil)


(defun cedille-mode-meta-var-text(mv)
  "Returns the text for the display of a single meta-variable MV"
  (if (cedille-mode-meta-var-solved mv)
      (concat (meta-var-name mv) " : " (meta-var-kind mv) " = " (meta-var-type mv))
    (concat (meta-var-name mv) " : " (meta-var-kind mv))))

(defun cedille-mode-display-meta-vars()
  (let ((parent cedille-mode-parent-buffer))
    (with-current-buffer (cedille-mode-meta-vars-buffer)
      (setq cedille-mode-parent-buffer parent
            buffer-read-only nil)
      (erase-buffer)
      (let ((meta-vars cedille-mode-meta-vars-list))
        (while meta-vars
          (insert (cedille-mode-meta-var-text (car meta-vars)) "\n")
          (setq meta-vars (cdr meta-vars))))
      (goto-char 1)
      (setq buffer-read-only t)
      (setq deactivate-mark nil))))



(defun cedille-mode-meta-vars()
  (cedille-mode-compute-meta-vars)
  (cedille-mode-display-meta-vars)
  (cedille-mode-rebalance-windows))

(defun cedille-mode-meta-vars-buffer-name()
  (with-current-buffer (or cedille-mode-parent-buffer (current-buffer))
    (concat "*cedille-meta-vars-" (file-name-base) "*")))

(defun cedille-mode-meta-vars-buffer()
  (get-buffer-create (cedille-mode-meta-vars-buffer-name)))


(define-minor-mode cedille-meta-vars-mode
  "Creates meta-vars-mode"
  nil
  " Meta-Vars"
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap)
    (define-key map (kbd "m") #'cedille-mode-close-active-window)
    (define-key map (kbd "M") #'cedille-mode-close-active-window)
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "meta-vars mode"))
    map)
  (when cedille-meta-vars-mode
    (set-input-method "Cedille")))

(provide 'cedille-mode-meta-vars)
