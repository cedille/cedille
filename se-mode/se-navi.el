
(defvar se-navi-keymaps nil
  "Association list for mapping major modes to navigation mode
key bindings.  Should not be accessed directly.")

(defvar se-navi-quit-on-change t
  "If non-nil, navigation mode will quit before a change is made
to the buffer.")

(make-variable-buffer-local
 (defvar se-navi-current-keymap nil
   "Lists current navigation mode's keymap."))

(defvar se-navi-nothing-map
  (let* ((keymap (make-sparse-keymap)))
    ;; all printable characters
    (suppress-keymap keymap t)
    ;; tab, backspace, enter
    (define-key keymap (kbd "<tab>")       #'se-navi-nothing)
    (define-key keymap (kbd "<backspace>") #'se-navi-nothing)
    (define-key keymap (kbd "<delete>")    #'se-navi-nothing)
    (define-key keymap (kbd "<return>")    #'se-navi-nothing)
    ;; prevent quoted inserts
    (define-key keymap [remap quoted-insert] #'se-navi-nothing)
    keymap)
  "A keymap to make a buffer weakly read-only.")

(define-minor-mode se-navigation-mode
  "Toggle Structure Editing's Navigation mode.
\\{se-navigation-mode-map}"
  :init-value nil
  :lighter " navi"
  :keymap (let ((map (make-sparse-keymap se-navi-nothing-map)))
	    (define-key map (kbd "c") #'se-inf-parse-file)
	    (define-key map (kbd "q") #'se-navigation-mode-quit)
	    (define-key map (kbd "e") #'se-mode-expand-selected)
	    (define-key map (kbd "s") #'se-mode-shrink-selected)
	    (define-key map (kbd "i") #'se-mode-inspect)
	    (define-key map (kbd "d") #'se-mode-inspect-destroy)
	    (define-key map (kbd "p") #'se-mode-select-previous)
	    (define-key map (kbd "n") #'se-mode-select-next)
	    (define-key map (kbd "h") #'se-navi-help)
	    (define-key map (kbd "w") #'copy-region-as-kill)
	    (define-key map (kbd "<tab>") #'back-to-indentation)
	    map)
  (when se-navigation-mode ;; activation
    ;; setup major-mode specific key bindings
    (setq se-navi-current-keymap (se-navi-get-keymap major-mode))
    (make-local-variable 'minor-mode-overriding-map-alist)
    (push (cons 'se-navigation-mode se-navi-current-keymap)
	  minor-mode-overriding-map-alist)

    (add-hook 'se-inf-post-parse-hook 'se-inf-process-spans)
    (add-hook 'se-inf-post-parse-hook 'se-inf-process-error t)
    (add-hook 'se-inf-post-parse-hook 'se-inf-process-error-span t)
    (add-hook 'deactivate-mark-hook 'se-navi-mark-deactivated-hook)

    ;; quit on change
    (when se-navi-quit-on-change
      (add-hook 'before-change-functions #'se-navigation-mode-quit nil t)))
  (unless se-navigation-mode ;; deactivation
    (kill-local-variable 'minor-mode-overriding-map-alist)
    (remove-hook 'deactivate-mark-hook 'se-navi-mark-deactivated-hook)
    (remove-hook 'before-change-functions #'se-navigation-mode-quit t)))

(defun se-navigation-mode-quit (&rest args)
  "Quits navigation mode."
  (interactive)
  (se-navigation-mode -1))

(defun se-navi-nothing ()
  "Does nothing.  Used in navigation mode keymaps."
  (interactive))

(defun se-navi-define-key (mode key def)
  "When activating se-navigation mode in a buffer, activate some
specific bindings for your major mode.

MODE is a symbol to be matched to the value of `major-mode'.  KEY
and DEF work the same as `define-key'."
  (let ((keymap (se-navi-get-keymap mode)))
    (define-key keymap key def)))

(defun se-navi-get-keymap (mode)
  "Returns navigation mode keymap associated with major mode
MODE.  Navigation mode keymaps will vary from usage of
`se-navi-define-key'."
  (or (cdr (assoc mode se-navi-keymaps))
      (let* ((keymap (make-sparse-keymap))
	     (entry (cons mode keymap)))
	(set-keymap-parent keymap se-navigation-mode-map)
	(add-to-list 'se-navi-keymaps entry)
	(cdr entry))))

(defun se-navi-help ()
  "Display navigation mode's keybindings."
  (interactive)
  (describe-mode)
  (with-current-buffer "*Help*"
    (goto-char (point-min))
    (when (search-forward "Se-Navigation" nil t)
      (push-button (1- (point))))))

(defun se-navi-documentation-advice (orig function &optional raw)
  "Advice for documentation.  ORIG is the original
`documentation' function.  FUNCTION and RAW correspond to
`documentation' arguments."
  (cond
   (raw
    (funcall orig function raw))
   ((equal #'se-navigation-mode function)
    ;; buffer defined in `describe-mode' in emacs >=21.1
    ;; using dynamic scoping is unwanted here, but most simple
    (with-current-buffer (if (boundp 'buffer) buffer (buffer-name))
      (substitute-command-keys
       (replace-regexp-in-string
	(regexp-quote "\\{se-navigation-mode-map}")
	(regexp-quote "\\{se-navi-current-keymap}")
	(documentation 'se-navigation-mode t)))))
   (t
    (funcall orig function raw))))

(if (fboundp #'advice-add)
    (advice-add 'documentation :around #'se-navi-documentation-advice))

(defun se-navi-mark-deactivated-hook ()
  "Sets `se-mode-selected' to nil so that the appearance matches reality"
  (se-mode-clear-selected))

(provide 'se-navi)
