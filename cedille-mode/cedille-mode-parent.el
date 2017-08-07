;;; Code for the parent keymap from which keymaps of other minor modes will be derived.

(require 'cl)

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
    (define-key map (kbd "M-c") #'cedille-mode-scratch-copy-buffer)
    (define-key map (kbd "f") #'cedille-mode-parent-forward)
    (define-key map (kbd "b") #'cedille-mode-parent-backward)
    (define-key map (kbd "a") #'cedille-mode-parent-first)
    (define-key map (kbd "l") #'cedille-mode-parent-last)
    (define-key map (kbd "j") #'cedille-mode-parent-jump)
    map))


(defun cedille-mode-parent-select-pin (pin)
  "Selects PIN"
  (let ((s (se-pin-item-start pin))
	(e (se-pin-item-end pin)))
    (goto-char s)
    (setq mark-active t)
    (push-mark e t t)))

(defun cedille-mode-parent-forward (start end)
  "Moves to the next jumpable text in the buffer"
  (interactive "r")
  (if (not mark-active)
      (cedille-mode-parent-forward-alt (point) (se-get-pins 'location))
    (let ((next (car (se-get-pins 'location nil end))))
      (if next
	  (cedille-mode-parent-select-pin next)
	(if cedille-mode-wrap-navigation
	    (cedille-mode-parent-first)
	  (message "No next"))))))

(defun cedille-mode-parent-backward (start end)
  "Moves to the previous jumpable text in the buffer"
  (interactive "r")
  (if (not mark-active)
      (cedille-mode-parent-backward-alt (point) (se-get-pins 'location))
    (let ((prev (car (last (se-get-pins 'location nil nil start)))))
      (if prev
	  (cedille-mode-parent-select-pin prev)
	(if cedille-mode-wrap-navigation
	    (cedille-mode-parent-last)
	  (message "No next"))))))

(defun cedille-mode-parent-first ()
  "Moves to the first jumpable text in the buffer"
  (interactive)
  (let ((pins (se-get-pins 'location)))
    (when pins
      (cedille-mode-parent-select-pin (car pins)))))

(defun cedille-mode-parent-last ()
  "Moves to the last jumpable text in the buffer"
  (interactive)
  (let ((pins (se-get-pins 'location)))
    (when pins
      (cedille-mode-parent-select-pin (car (last pins))))))

(defun cedille-mode-parent-forward-alt (pos pins)
  "Called when the mark is not active and the user presses f"
  (let ((pins (remove-if (lambda (pin) (> pos (se-pin-item-end pin))) pins)))
    (if pins
	(cedille-mode-parent-select-pin (car pins))
      (if cedille-mode-wrap-navigation
	  (cedille-mode-parent-first)
	(message "No next")))))

(defun cedille-mode-parent-backward-alt (pos pins)
  "Called when the mark is not active and the user presses b"
  (let ((pins (remove-if (lambda (pin) (< pos (se-pin-item-start pin))) pins)))
    (if pins
	(cedille-mode-parent-select-pin (car (last pins)))
      (if cedille-mode-wrap-navigation
	  (cedille-mode-parent-last)
	(message "No previous")))))

(defun cedille-mode-parent-jump (start end)
  "If jumpable text is selected, jump to its definition"
  (interactive "r")
  (let ((pin (se-pins-at start end 'location)))
    (when (and mark-active pin)
      (setq data (se-pin-item-data (car pin))
	    filename (cdr (assoc "filename" data))
	    pos (string-to-number (cdr (assoc "pos"  data)))
	    continue (lambda ()
		       (setq past (car cedille-mode-browsing-history)
			     present (buffer-file-name))
		       (with-current-buffer (find-file filename)
			 (setq cedille-mode-browsing-history (cons (cons present past) nil))
			 (goto-char pos)
			 (se-navigation-mode))
		       (cedille-mode-rebalance-windows)))
      (condition-case err
	  (while (null (buffer-file-name)) (delete-window))
	(error err))
      (funcall continue))))

(provide 'cedille-mode-parent)
