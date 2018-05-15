;;; Code for the parent keymap from which keymaps of other minor modes will be derived.

(require 'cl)

(make-variable-buffer-local
 (defvar cedille-mode-parent-buffer nil))

(defmacro make-cedille-mode-resize-current-window (amount)
  "Creates a function that resizes the window associated with buffer by amount and then locks the size of the window"
  `(lambda()
     (interactive)
     (with-current-buffer (current-buffer)
       (window-resize nil ,amount))))

(defmacro cedille-mode-parent-region-cmd (region-cmd)
  "Ensures that there is a region before interactively calling REGION-CMD"
  `(lambda ()
     (interactive)
     (unless (mark)
       (push-mark ,1 ,t))
     (call-interactively ,region-cmd)))

(defun cedille-mode-unlock-current-window-size()
  "Allows selected window to be resized, then restores it to the minimal size"
  (interactive)
  (cedille-mode-rebalance-windows))
  ;(with-current-buffer (current-buffer)
  ;  (fit-window-to-buffer)))

(defmacro cedille-mode-parent-interactive (code)
  "Normalizes the selected region"
  `(lambda ()
     (interactive)
     (if (region-active-p)
         (let ((str (buffer-substring (region-beginning) (region-end))))
           (with-current-buffer cedille-mode-parent-buffer
             (with-selected-window (get-buffer-window)
               (case ,code
                 (1 (cedille-mode-normalize-send-prompt str t))
                 (2 (cedille-mode-normalize-send-prompt str nil))
                 (3 (cedille-mode-erase-send-prompt str))
                 (4 (cedille-mode-br-prompt str))))))
       (message "No region selected"))))

(defvar cedille-mode-minor-mode-parent-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "+") (make-cedille-mode-resize-current-window 1))  ; increase and lock size of window
    (define-key map (kbd "-") (make-cedille-mode-resize-current-window -1)) ; decrease and lock size of window
    (define-key map (kbd "=") #'cedille-mode-unlock-current-window-size)    ; unlock size of window then resizes it
    (define-key map (kbd "M-c") #'cedille-mode-scratch-copy-buffer)
    (define-key map (kbd "f") (cedille-mode-parent-region-cmd #'cedille-mode-parent-forward))
    (define-key map (kbd "b") (cedille-mode-parent-region-cmd #'cedille-mode-parent-backward))
    (define-key map (kbd "a") (cedille-mode-parent-region-cmd #'cedille-mode-parent-first))
    (define-key map (kbd "e") (cedille-mode-parent-region-cmd #'cedille-mode-parent-last))
    (define-key map (kbd "j") (cedille-mode-parent-region-cmd #'cedille-mode-parent-jump))
    (define-key map (kbd "C-i n") (cedille-mode-parent-interactive 1))
    (define-key map (kbd "C-i h") (cedille-mode-parent-interactive 2))
    (define-key map (kbd "C-i e") (cedille-mode-parent-interactive 3))
    (define-key map (kbd "C-i b") (cedille-mode-parent-interactive 4))
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
      (cedille-mode-parent-forward-alt (point) (se-get-pins 'loc))
    (let ((next (car (se-get-pins 'loc nil end))))
      (if next
	  (cedille-mode-parent-select-pin next)
	(if cedille-mode-wrap-navigation
	    (cedille-mode-parent-first)
	  (message "No next"))))))

(defun cedille-mode-parent-backward (start end)
  "Moves to the previous jumpable text in the buffer"
  (interactive "r")
  (if (not mark-active)
      (cedille-mode-parent-backward-alt (point) (se-get-pins 'loc))
    (let ((prev (car (last (se-get-pins 'loc nil nil start)))))
      (if prev
	  (cedille-mode-parent-select-pin prev)
	(if cedille-mode-wrap-navigation
	    (cedille-mode-parent-last)
	  (message "No next"))))))

(defun cedille-mode-parent-first ()
  "Moves to the first jumpable text in the buffer"
  (interactive)
  (let ((pins (se-get-pins 'loc)))
    (when pins
      (cedille-mode-parent-select-pin (car pins)))))

(defun cedille-mode-parent-last ()
  "Moves to the last jumpable text in the buffer"
  (interactive)
  (let ((pins (se-get-pins 'loc)))
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
  (let ((pin (se-pins-at start end 'loc)))
    (when (and mark-active pin)
      (setq data (se-pin-item-data (car pin))
	    filename (cdr (assoc 'fn data))
	    pos (string-to-number (cdr (assoc 'pos data))))
      (select-window (cedille-mode-parent-main-window))
      (setq past (car cedille-mode-browsing-history)
	    present (buffer-file-name))
      (with-current-buffer (find-file filename)
	(setq cedille-mode-browsing-history (cons (cons present past) nil))
	(cedille-mode-parent-jump-to-pos pos)
	(se-navigation-mode))
      (cedille-mode-rebalance-windows))))

(defun cedille-mode-parent-jump-to-pos (pos)
  "Jumps in the current file to pos"
  (goto-char pos)
  (when mark-active (deactivate-mark)))

(defun cedille-mode-parent-main-buffer ()
  "Returns the last selected buffer with a file associated with it"
  (window-buffer (cedille-mode-parent-main-window)))

(defun cedille-mode-parent-main-window ()
  "Returns the last selected window with a file associated with it"
  (cedille-mode-parent-main-window-h (get-buffer-window) (length (window-list)) 0))

(defun cedille-mode-parent-main-window-h (window max n)
  "Helper for `cedille-mode-parent-window-buffer'"
  (if (>= max n)
    (if (buffer-file-name (window-buffer window))
	window
      (cedille-mode-parent-main-window-h (previous-window window) max (+ 1 n)))
    (cedille-mode-get-create-window)))

(provide 'cedille-mode-parent)
