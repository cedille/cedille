;;; Code for the parent keymap from which keymaps of other minor modes will be derived.

(defmacro make-cedille-mode-resize-current-window (amount)
  "Creates a function that resizes the window associated with buffer by amount"
  `(lambda() (interactive) (window-resize nil ,amount)))

(defvar cedille-mode-minor-mode-parent-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "+") (make-cedille-mode-resize-current-window 1))  ; increase size of window
    (define-key map (kbd "-") (make-cedille-mode-resize-current-window -1)) ; decrease size of window
    map))

(provide 'cedille-mode-parent)
