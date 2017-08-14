(defmacro make-cedille-mode-customize(group)
  "Creates a function that takes the user to the 
customization page associated with the current 
window and also expands the current window to a
reasonable size"
  `(lambda()
     (interactive)
     (customize-group-other-window ,group)))

(provide 'cedille-mode-customize)
