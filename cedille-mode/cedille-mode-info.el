;;; For the purpose of bringing up the info documentation
;;; in cedille-mode
;;;

(defun cedille-mode-info-path() "Returns the path for the info pages" (concat cedille-path "/docs/info/cedille-info-main.info"))

(defmacro make-cedille-mode-info-display-page(node)
  "Makes a function that opens the info file and (optionally) jumps to a particular node."
  `(lambda nil
     (interactive)
     (info-other-window
      (if ,node
	  (concat "(" (cedille-mode-info-path) ")" ,node)
	(cedille-mode-info-path))
      "*cedille-mode-info*")))

;;(defun cedille-mode-info-display()
;;    "Displays the info pages for Cedille"
;;    (interactive)
;;    (info (cedille-mode-info-path))
;;    (Info-menu "cedille-mode commands")
;;)


(provide 'cedille-mode-info)
