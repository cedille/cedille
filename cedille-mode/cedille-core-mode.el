


;(require 'se)
;(require 'se-mode)
;(require 'se-navi)
;(require 'se-inf)
;(require 'se-markup)

(make-variable-buffer-local
 (defvar cdle-mode-process nil))

(make-variable-buffer-local
 (defvar cdle-mode-running nil))

(defvar cdle-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "M-s") #'cdle-mode-toggle)
    map))

(defun cdle-mode-toggle ()
  "Check the current file, or if it is already checking, kill and restart the process"
  (interactive)
  (if cdle-mode-running
    (progn
      (kill-process cdle-mode-process)
      (message "Process killed")
      (cdle-mode 0)
      (cdle-mode 1))
    (let ((cmd (concat cedille-core-program-name " -b " (buffer-file-name))))
                    ;(shell-quote-argument " -b ")
                    ;(shell-quote-argument (buffer-file-name)))))
      (message "Checking...")
      (setq cdle-mode-process (start-process-shell-command "cdle-mode" "*cdle-mode*" cmd))
      (set-process-sentinel cdle-mode-process #'cdle-mode-sentinel)))
  (setq cdle-mode-running (not cdle-mode-running)))

(defun cdle-mode-sentinel (process msg)
  "Sentinel for the Cedille Core process"
  ;(message "anyway code: %s" (process-exit-status process))
  (case (process-exit-status process)
    (0 (message "Checks!"))
    (1 (message "Error—unknown option %s" (process-exit-status process)))
    (2 (message "Parse error"))
    (3 (message "Error reading file"))
    (4 (message "Type error"))
    (t (message "Oops—this shouldn't happen! Process signaled code %s with message \"%s\"" (process-exit-status process) msg))
    )
  (setq cdle-mode-running nil))

(defun cdle-mode-help ()
  "Display help regarding cdle mode"
  (interactive)
  (make-cedille-mode-info-display-page "cdle mode"))

(define-minor-mode cdle-mode
  "Minor mode for Cedille Core (.cdle) files"
  :init-value nil
  :lighter " cdle"
  :keymap cdle-keymap
  (when cdle-mode
    (set-input-method "Cedille")))
;    (make-local-variable 'minor-mode-overriding-map-alist)
;    (push (cons 'se-navigation-mode se-navi-current-keymap) minor-mode-overriding-map-alist)))

(autoload 'cdle-mode "cdle-mode" "Minor mode for Cedille Core (.cdle) files" t)
(modify-coding-system-alist 'file "\\.cdle\\'" 'utf-8)
(add-to-list 'auto-mode-alist (cons "\\.cdle\\'" 'cdle-mode))


(provide 'cedille-core-mode)
