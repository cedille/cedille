;;; cedille-mode.el --- Major mode for Cedille
;;;
;;; Add something like the following to your .emacs file to load this
;;; mode for .ced files:
;;;
;;;   (autoload 'cedille-mode "cedille-mode" "Major mode for editing cedille files ." t)
;;;   (add-to-list 'auto-mode-alist '("\\.ced\\'" . cedille-mode))
;;;
;;; You will need to link or copy this file to a load directory for emacs.
;;; I have this in my .emacs file to make ~/.emacs.d such a directory:
;;;
;;;   (add-to-list 'load-path "/home/astump/.emacs.d/")
;;;
;;;

;;; stlc-mode.el --- Major mode for Stlc

;;; Commentary:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Dependency

;;; Code:

(require 'quail)

(when (version< emacs-version "24.4")
  (defun define-error (name message &optional parent)
    "Define NAME as a new error signal.
MESSAGE is a string that will be output to the echo area if such an error
is signaled without being caught by a `condition-case'.
PARENT is either a signal or a list of signals from which it inherits.
Defaults to `error'."
    (unless parent (setq parent 'error))
    (let ((conditions
           (if (consp parent)
               (apply #'nconc
                      (mapcar (lambda (parent)
                                (cons parent
                                      (or (get parent 'error-conditions)
                                          (error "Unknown signal `%s'" parent))))
                              parent))
             (cons parent (get parent 'error-conditions)))))
      (put name 'error-conditions
           (delete-dups (copy-sequence (cons name conditions))))
      (when message (put name 'error-message message)))))

(require 'se-mode)
(eval-when-compile (require 'se-macros))

(defvar cedille-mode-version "1.0"
  "The version of the cedille mode.")

(defvar cedille-mode-debug nil
  "Show debugging spans in cedille mode.")

; set in .emacs file
(defvar cedille-program-name "cedille-executable"
  "Program to run for cedille mode.")

(defvar cedille-info-buffer-trailing-edge 1 "Number of blank lines to insert at the bottom of the info buffer.")

(defun cedille-info-buffer-name() (concat "*cedille-info-" (file-name-base (buffer-name)) "*"))

(defun cedille-info-buffer()
  (let* ((n (cedille-info-buffer-name))
         (b (get-buffer-create n)))
    (with-current-buffer b
       (setq buffer-read-only nil))
    b))

(defun cedille-adjust-info-window-size()
  (let ((w (get-buffer-window (cedille-info-buffer))))
   (when w
     (fit-window-to-buffer w)
     (window-resize w cedille-info-buffer-trailing-edge))))

(defun cedille-mode-concat-sep(sep ss)
  "Concat the strings in nonempty list ss with sep in between each one."
  (let ((he (car ss))
        (ta (cdr ss)))
    (if (not ta) he
      (concat he sep (cedille-mode-concat-sep sep ta)))))

(defun cedille-mode-split-string(s)
  "Return a pair of the prefix of the string up to the first space, 
and the remaining suffix."
  (let ((ss (split-string s " ")))
    (if (< (length ss) 2) s
      (cons (car ss) (cedille-mode-concat-sep " " (cdr ss))))))

(defun cedille-mode-get-seqnum(a)
  "Get the seqnum from a json pair. The second component
is assumed to be a string with a sequence number (prefix up
 to the first space in each string)."
  (car (cedille-mode-split-string (cdr a))))

(defun cedille-mode-compare-seqnums(a b)
  "Compare two pairs by seqnum."
  (let ((na (cedille-mode-get-seqnum a))
        (nb (cedille-mode-get-seqnum b)))
      (< (string-to-number na) (string-to-number nb))))

(defun cedille-mode-strip-seqnum(s)
  "Return a new string just like s except without the prefix up to the 
first space."
  (cdr (cedille-mode-split-string s)))

(defun cedille-mode-sort-and-strip-json(json)
  "Sort the pairs in the JSON data by the number at the 
start of each string, and then strip out that number."
  (when json
    (let ((name (assoc 'name json)))
      (setq json 
          (loop for (key . value) in json
            unless (or (eq key 'start) (eq key 'end) (eq key 'name))
            collecting (cons key value)))
      (setq json (sort json 'cedille-mode-compare-seqnums))
      (setq json (loop for (key . value) in json
                   collecting (cons key (cedille-mode-strip-seqnum value))))
      (setq json (cons name json))
      json)))

;  (unless (and (not cedille-mode-debug) (string= (cdr name) "Debug")) ; unless not in debug mode but this is a debug span

(defun cedille-mode-inspect ()
  "Displays information on the currently selected node in 
the info buffer for the file.  Return the info buffer as a convenience."
  (interactive)
  (let ((b (cedille-info-buffer))
        (txt (if se-mode-selected
               (se-mode-pretty-json (cedille-mode-sort-and-strip-json (se-term-to-json (se-mode-selected))))
               "\n")))
    (with-current-buffer b (erase-buffer) (insert txt) (setq buffer-read-only t))
    (cedille-adjust-info-window-size)
    (setq deactivate-mark nil)
    b))

(defun se-mode-pretty-json (json)
  "Prints a table in a more human readable form. Does not handle
recursion or anything other than key-value pairs."
  (when json
    (let (max fstr)
      (loop for (key . value) in json
	    maximizing (length (format "%s" key)) into maxlen
	    finally (setq max maxlen))
      (setq fstr (format "%%%ds:\t%%s\n" max))
      (loop for (key . value) in json
	    collecting (format fstr key value) into lines
	    finally (return (apply #'concat lines))))))

(defun se-mode-left-spine(node)
  "Find the path down the left spine of the node."
  (let ((kids (se-node-children node)))
    (cons node
     (when kids
       (se-mode-left-spine (first kids))))))

(defun se-mode-update-selected(path)
  "Update the se-mode-selected and se-mode-not-selected variables,
from the given path."
  (let ((path (nreverse path)))
    (setq se-mode-not-selected path)
    ; the call to cdr is to drop the node "car path" from the list, since it is already included in se-mode-not-selected
    (setq se-mode-selected (when path (cdr (se-mode-left-spine (car path)))))))

(defun se-mode-set-spans ()
  "Used by `se-mode' methods to set `se-mode-selected' and
`se-mode-not-selected'."
  (unless mark-active
    (se-mode-clear-selected))
  (when (and (null se-mode-selected)
	     (null se-mode-not-selected))
    (se-mode-update-selected (se-find-point-path (point) (se-mode-parse-tree)))))

(defun se-mode-select (term)
  "Updates selection path and selects region."
  (when term
    (se-mode-update-selected (se-find-span-path term (se-mode-parse-tree)))
    (se-mode-expand-selected)
    t))

(defun se-mode-shrink-selected ()
  "Shrink the selected region.  If a smaller region was previous
selected, select it again."
  (interactive)
  (se-mode-set-spans)
  (when se-mode-selected
    (push (pop se-mode-selected) se-mode-not-selected))
  (if se-mode-selected
      (se-mode-mark-term (se-mode-selected))
    (message "No child span found")))

(defun se-mode-select-last-helper (prev)
  "Helper function for selecting the last sibling span from a node 
of the tree."
  (let ((next (se-mode-next)))
    (if (null next) prev
      (se-mode-select next)
      (se-mode-select-last-helper next))))
  
(defun se-mode-select-last()
  "Selects the last sibling of the parent of the current node."
  (interactive)
  (se-mode-select-last-helper (se-mode-selected)))

(defun se-mode-select-first-helper (next)
  "Helper function for selecting the first sibling span from a node 
of the tree."
  (let ((prev (se-mode-previous)))
    (if (null prev) next
      (se-mode-select prev)
      (se-mode-select-first-helper prev))))
  
(defun se-create-parse-tree (lst)
  "Forms a tree from a sorted list of spans.  Returns nil if data is ill
formatted."
  ;; `copy-list' could be used; however, it isn't expected a user will
  ;; reuse a span list (or care if it becomes sorted).
  (let ((len (length lst))
	(spans (copy-list lst))
	(parents nil))
    (se--sorted-spans-to-tree)))


(defun se-mode-select-first()
  "Selects the first sibling of the parent of the current node."
  (interactive)
  (se-mode-select-first-helper (se-mode-selected)))

(make-variable-buffer-local
 (defvar se-mode-spans nil
   "The spans obtained from the backend tool for `se-mode'
methods."))

(defun se-inf-process-spans (json)
  "Creates parse tree from spans found in JSON. Sets the variables
`se-mode-parse-tree' and `se-mode-spans'."
  (when (se-inf-get-spans json)
    (setq se-mode-spans 
          (sort (se-create-spans (se-inf-get-spans json)) 'se-term-before-p))
    (setq se-mode-parse-tree
	  (se-create-parse-tree se-mode-spans))))

(make-variable-buffer-local
 (defvar cedille-mode-next-errors nil
   "Next spans with an error value."))

(make-variable-buffer-local
 (defvar cedille-mode-cur-error nil
   "The currently selected error span."))

(make-variable-buffer-local
 (defvar cedille-mode-prev-errors nil
   "Previously seen spans with an error value."))

(defun cedille-span-has-error-data(data)
  "Return t if the span has error data, and nil otherwise."
  (assoc 'error data))

(defun cedille-find-error-spans(spans)
  "Sets `cedille-mode-error-spans' to hold a list
of spans that have an error value."
  (when spans
    (let ((cur (car spans)))
      (when (cedille-span-has-error-data (se-span-data cur))
        (push cur cedille-mode-next-errors))
      (cedille-find-error-spans (cdr spans)))))
    
(defun cedille-mode-set-error-spans(response)
  "After loading spans from the backend tool, this hook will look for error
spans and set the variable `cedille-mode-error-spans'.  The input is ignored."
  (setq cedille-mode-next-errors nil)
  (setq cedille-mode-prev-errors nil)
  (setq cedille-mode-cur-error nil)
  (cedille-find-error-spans se-mode-spans)
  (setq cedille-mode-next-errors (reverse cedille-mode-next-errors)) ; we are pushing the errors as we find them, so the list is reversed
)

(defun cedille-mode-any-errors()
  "Return t iff there are any errors."
  (or cedille-mode-next-errors cedille-mode-prev-errors cedille-mode-cur-error))

(defun cedille-mode-select-span(cur)
  "Select and the given span."
   (se-mode-update-selected (se-find-span-path cur (se-mode-parse-tree)))
   (se-mode-mark-term cur)
   (push (pop se-mode-not-selected) se-mode-selected)
   (display-buffer (cedille-mode-inspect)))

(defun cedille-mode-select-next-error()
  "Select the next error if any, and display the info buffer."
  (interactive)
  (if (null cedille-mode-next-errors)
     (if (and (not (se-mode-selected)) cedille-mode-cur-error) (cedille-mode-select-span cedille-mode-cur-error)
       (message (if (cedille-mode-any-errors) "No further errors" "No errors")))
     (let ((cur (pop cedille-mode-next-errors)))
       (when cedille-mode-cur-error (push cedille-mode-cur-error cedille-mode-prev-errors))
       (setq cedille-mode-cur-error cur)
       (cedille-mode-select-span cur))))

(defun cedille-mode-select-previous-error()
  "Select the previous error if any, and display the info buffer."
  (interactive)
  (if (null cedille-mode-prev-errors)
     (if (and (not (se-mode-selected)) cedille-mode-cur-error) (cedille-mode-select-span cedille-mode-cur-error)
       (message (if (cedille-mode-any-errors) "No previous errors" "No errors")))
     (let ((cur (pop cedille-mode-prev-errors)))
       (when cedille-mode-cur-error (push cedille-mode-cur-error cedille-mode-next-errors))
       (setq cedille-mode-cur-error cur)
       (cedille-mode-select-span cur))))

(defun cedille-mode-select-next()
  "Selects the next sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-next)
  (cedille-mode-inspect))

(defun cedille-mode-select-previous()
  "Selects the previous sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-previous)
  (cedille-mode-inspect))

(defun cedille-mode-select-parent()
  "Selects the parent of the currently selected node in 
the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-expand-selected)
  (cedille-mode-inspect))

(defun cedille-mode-select-first-child()
  "Selects the first child of the lowest node in the parse tree
containing point, and updates the Cedille info buffer."
  (interactive)
  (se-mode-shrink-selected)
  (cedille-mode-inspect))

(defun cedille-mode-select-first()
  "Selects the first sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-first)
  (cedille-mode-inspect))

(defun cedille-mode-select-last()
  "Selects the last sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-last)
  (cedille-mode-inspect))

(defun cedille-mode-toggle-info()
  "Shows or hides the Cedille info buffer."
  (interactive)
  (let* ((b (cedille-info-buffer))
         (w (get-buffer-window b)))
    (if w (delete-window w) (display-buffer b) (cedille-adjust-info-window-size))))

(defun cedille-mode-quit()
  "Quit Cedille navigation mode"
  (interactive)
  (se-mode-clear-selected)
  (se-navigation-mode-quit))

; se-navi-define-key maintains an association with the major mode,
; so that different major modes using se-navi-define-key can have
; separate keymaps.
(defun cedille-modify-keymap()
  (se-navi-define-key 'cedille-mode (kbd "f") #'cedille-mode-select-next)
  (se-navi-define-key 'cedille-mode (kbd "b") #'cedille-mode-select-previous)
  (se-navi-define-key 'cedille-mode (kbd "p") #'cedille-mode-select-parent)
  (se-navi-define-key 'cedille-mode (kbd "n") #'cedille-mode-select-first-child)
  (se-navi-define-key 'cedille-mode (kbd "g") #'se-mode-clear-selected)
  (se-navi-define-key 'cedille-mode (kbd "q") #'cedille-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "\M-s") #'cedille-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "\C-g") #'cedille-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "e") #'cedille-mode-select-last)
  (se-navi-define-key 'cedille-mode (kbd "a") #'cedille-mode-select-first)
  (se-navi-define-key 'cedille-mode (kbd "i") #'cedille-mode-toggle-info)
  (se-navi-define-key 'cedille-mode (kbd "r") #'cedille-mode-select-next-error)
  (se-navi-define-key 'cedille-mode (kbd "R") #'cedille-mode-select-previous-error)
  (se-navi-define-key 'cedille-mode (kbd "s") nil)
)

(cedille-modify-keymap)

(se-create-mode "Cedille" nil
  "Major mode for Cedille files."

  (setq-local comment-start "%")
  
  (se-inf-start
   (or (get-buffer-process "*cedille-mode*") ;; reuse if existing process
       (start-process "cedille-mode" "*cedille-mode*" cedille-program-name)))

  (set-input-method "Cedille")
)

(setq se-inf-response-hook (nconc se-inf-response-hook (list 'cedille-mode-set-error-spans)))

(modify-coding-system-alist 'file "\\.ced\\'" 'utf-8)

(quail-define-package "Cedille" "UTF-8" "δ" t ; guidance
		      "Cedille input method."
		      nil nil nil nil nil nil t) ; maximum-shortest

(mapc (lambda (pair) (quail-defrule (car pair) (cadr pair) "Cedille"))
	'(("\\l" "λ") ("\\L" "Λ") ("\\>" "→") ("\\r" "→") ("\\a" "∀") ("\\B" "□") ("\\P" "Π") 
          ("\\s" "★") ("\\S" "☆") ("\\." "·") ("\\f" "⇐") ("\\u" "↑") 
          ("\\h" "●") ("\\k" "𝒌") ("\\i" "ι") ("\\=" "≃") 
          ("\\b" "β") ("\\e" "ε") ("\\rr" "ρ") ("\\y" "ς") ("\\t" "θ") ("\\T" "θ̄")))

(provide 'cedille-mode)
;;; cedille-mode.el ends here

