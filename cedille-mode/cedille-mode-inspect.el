;;;;INSPECT MODE
;;; This document contains code related to cedille inspect mode.
;;; This mode, called using the hotkey 'i', provides information about the selected span

;;TODO - make sure upon opening inspect mode that it goes to position 1

(require 'se-mode)

(load-library "cedille-mode-parent")

;(make-variable-buffer-local
; (defvar cedille-inspect-span nil
; "The span that the inspect buffer is currently showing"))

(define-minor-mode cedille-inspect-view-mode
  "Creates inspect mode, which displays information about the current node"
  nil         ; init-value, whether the mode is on automatically after definition
  " Context"  ; indicator for mode line
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map cedille-mode-minor-mode-parent-keymap) ; inherit bindings from parent keymap
    (define-key map (kbd "i") #'cedille-mode-close-active-window) ; exit inspect mode
    (define-key map (kbd "I") #'cedille-mode-close-active-window) ; exit inspect mode
    ;(define-key map (kbd "r") #'cedille-mode-inspect-remove-interactive-line)
    map))

(defun cedille-mode-inspect-buffer-name() (concat "*cedille-inspect-" (file-name-base (buffer-name)) "*"))

(defun cedille-mode-inspect-buffer()
  (let* ((n (cedille-mode-inspect-buffer-name))
         (b (get-buffer-create n)))
    ;(with-current-buffer b
    ;   (setq buffer-read-only nil))
    b))

(defun cedille-mode-inspect ()
  "Displays information on the currently selected node in 
the info buffer for the file.  Return the info buffer as a convenience."
  (when se-mode-selected
    (let* ((span (se-mode-selected))
	   (buffer (cedille-mode-inspect-buffer))
           (d (se-term-to-json span))
           (txt (se-mode-pretty-json-interactive (if cedille-mode-debug d (cedille-mode-filter-out-special d)))))
      (with-current-buffer buffer
	(setq buffer-read-only nil)
	(cedille-inspect-view-mode)
	;(setq cedille-inspect-span span)
	(erase-buffer)
	(insert txt)
	(goto-char 1)
	(setq buffer-read-only t))
      (cedille-mode-rebalance-windows)
      (setq deactivate-mark nil)
      buffer)))

(defun cedille-mode-inspect-clear-all ()
  (interactive)
  (se-pin-clear-all 'se-interactive)
  (se-mapc 'se-inf-clear-span-interactive (se-mode-parse-tree))
  (cedille-mode-inspect))

(defun cedille-mode-inspect-clear ()
  (interactive)
  (when se-mode-selected
    (setq span (se-first-span (se-mode-selected)))
    (setq s (se-span-start span))
    (setq e (se-span-end span))
    (se-unpin-list (se-pins-at s e 'se-interactive))
    (se-inf-clear-span-interactive span))
  (cedille-mode-inspect))

;(defun cedille-mode-inspect-remove-interactive-line ()
;  "Removes the interactive attribute associated with the line the mark is on"
;  (interactive)
;  (when cedille-inspect-span
;    (setq line (- (count-lines 1 (mark)) 1))
;    (setq split (split-string (buffer-string) "\n"))
;    (setq str-line (nth line split))
;    (message "str-line: %s, line: %s" str-line line)
;    (setq str (cedille-mode-inspect-remove-ws str-line))
;    (message "removed ws: %s" str)
;    (setq symbol-str (cedille-mode-inspect-up-to-char str ":"))
;    (setq symbol (make-symbol symbol-str))
;    (setq span (se-first-span cedille-inspect-span))
;    (setq ints (assoc 'se-interactive (se-span-data span)))
;    (assq-delete-all symbol ints)
;    ))

;(defun cedille-mode-inspect-up-to-char (str chr)
;  "Returns the str until it reaches char"
;  (cedille-mode-inspect-up-to-char-h str chr '()))

;(defun cedille-mode-inspect-up-to-char-h (str chr acc)
;  "Helper for `cedille-mode-inspect-up-to-char'"
;  (if (string= str "")
;      (concat (reverse acc))
;      (setq h (string-to-char str))
;      (if (string= (string h) chr)
;	  (concat (reverse acc))
;	  (cedille-mode-inspect-up-to-char-h (substring str 1) chr (cons h acc));)))

;(defun cedille-mode-inspect-remove-ws (str)
;  "Removes the proceeding whitespaces in str"
;  (unless (string= str "")
;    (setq h (string-to-char str))
;    (if (string= (string h) " ")
;	(cedille-mode-inspect-remove-ws (substring str 1))
;        str)))

(provide 'cedille-mode-inspect)
