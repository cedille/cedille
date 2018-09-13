;;; For the purpose of bringing up the info documentation
;;; in cedille-mode
;;;

(defmacro make-cedille-mode-info-display-page(node)
  "Makes a function that opens the info file and (optionally) jumps to a particular node."
  `(lambda nil
     (interactive)
     (info-other-window
      (if ,node
	  (concat "(" cedille-path-docs ")" ,node)
	cedille-path-docs)
      "*cedille-mode-info*")))

;;(defun cedille-mode-info-display()
;;    "Displays the info pages for Cedille"
;;    (interactive)
;;    (info (cedille-mode-info-path))
;;    (Info-menu "cedille-mode commands")
;;)


(provide 'cedille-mode-info)
