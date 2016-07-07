;;; For the purpose of bringing up the info documentation
;;; in cedille-mode
;;;
;;;
;;; Add this line to the cedille-mode.el to bind the key:
;;; (se-navi-define-key 'cedille-mode (kbd "h") #'cedille-mode-info-display)

(defun cedille-mode-info-path()
    "Returns the path for the info pages"
    (concat cedille-path "docs/info/cedille-info-main.info")
)

(defun cedille-mode-info-display()
    "Displays the info pages for Cedille"
    (interactive)
    (info (cedille-mode-info-path))
)


(provide 'cedille-mode-info)
