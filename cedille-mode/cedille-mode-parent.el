;;; Code for the parent keymap from which keymaps of other minor modes will be derived.

(defmacro make-cedille-mode-resize-current-window (amount)
  "Creates a function that resizes the window associated with buffer by amount and then locks the size of the window"
  `(lambda()
     (interactive)
     (with-current-buffer (current-buffer) (setq window-size-fixed nil))
     (window-resize nil ,amount)
     (with-current-buffer (current-buffer) (setq window-size-fixed t))))

(defun cedille-mode-unlock-current-window-size()
  "Allows selected window to be resized, then restores it to the minimal size"
  (interactive)
  (with-current-buffer (current-buffer) (setq window-size-fixed nil))
  (fit-window-to-buffer))

(defvar cedille-mode-minor-mode-parent-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "+") (make-cedille-mode-resize-current-window 1))  ; increase and lock size of window
    (define-key map (kbd "-") (make-cedille-mode-resize-current-window -1)) ; decrease and lock size of window
    (define-key map (kbd "=") #'cedille-mode-unlock-current-window-size)    ; unlock size of window then resizes it
    map))

(defun rev-h (list reversed)
  "Helper for `rev'"
  (if (endp list) reversed (rev-h (rest list) (list* (first list) reversed))))

(defun rev (list)
  "Reverses a list"
  (rev-h list '()))

(provide 'cedille-mode-parent)
