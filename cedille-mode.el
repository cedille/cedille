;;; cedille-mode.el --- Major mode for Cedille
;;;
;;; You need to set cedille-path to be the path to your Cedille installation.
;;; Then add that path to your load path for emacs.
;;; Then put (require 'cedille-mode) in your .emacs file. 
;;; 
;;; For example:
;;;
;;;    (setq cedille-path "/home/astump/cedille")
;;;    (add-to-list 'load-path cedille-path)
;;;    (require 'cedille-mode)
;;;

(require 'quail)

;(defvar cedille-program-name (concat cedille-path "/mock-cedille.sh"))
(defvar cedille-program-name (concat cedille-path "/cedille"))
(setq max-lisp-eval-depth 30000)
(setq max-specpdl-size 30000)

(defvar cedille-mode-browsing-history '(nil nil)) ;stores history while jumping between files

(autoload 'cedille-mode "cedille-mode" "Major mode for editing cedille files ." t)
(add-to-list 'auto-mode-alist (cons "\\.ced\\'" 'cedille-mode))

(let ((se-path (concat cedille-path "/se-mode")))
  (add-to-list 'load-path se-path)
  (add-to-list 'load-path (concat se-path "/json.el")))
(load-library "se")

(let ((cedille-mode-library-path (concat cedille-path "/cedille-mode")))
  (add-to-list 'load-path cedille-mode-library-path)
  (add-to-list 'load-path (concat cedille-mode-library-path "/json.el")))
(load-library "cedille-mode-library")

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

;;-----------------------------------------------------------------------------
;;   Customization

(defgroup cedille nil
  "Major mode for developing Cedille programs."
  :group 'languages)


(defcustom cedille-mode-debug nil
  "If non-nil then print extra attributes intended for developers, in the inspect buffer"
  :type '(boolean)
  :group 'cedille)

(defcustom cedille-mode-autohighlight-matching-variables t
  "If non-nil then whenever a variable is highlighted, all matching variables (sensitive to scope) will be highlighted as well."
  :type '(boolean)
  :group 'cedille)


;; ----------------------------------------------------------------------------



(defvar cedille-mode-highlight-spans nil
  "Spans including spans marked not-for-navigation.")


					; UTILITY FUNCTIONS FOR MANAGING WINDOWS

(defun cedille-mode-get-create-window(buffer)
  "Retrieves the window associated with the given buffer or else creates a new window and fills it with the buffer"
  (let ((window (get-buffer-window buffer)))
    (if window
	window
      (let ((window (split-window)))
	   (set-window-buffer window buffer)
	   window))))

(defun cedille-mode-toggle-buffer-display(buffer)
  "Toggles display of buffer on or off. Returns nil if window was deleted, or the window if it was created."
  (let ((window (get-buffer-window buffer)))
    (if window
	(progn
	  (delete-window window)
	  (cedille-mode-rebalance-windows))
      (let ((window (cedille-mode-get-create-window buffer)))
	(cedille-mode-rebalance-windows)
	window))))

(defun cedille-mode-rebalance-windows()
  "Resizes all windows"
  (walk-windows (lambda (window) (fit-window-to-buffer window))))

(defun cedille-mode-close-active-window() (interactive) (delete-window))

					;UTILITY FUNCTIONS FOR MANAGING BUFFERS

(defun cedille-mode-update-buffers()
  "Update the info and context buffers."
  (cedille-mode-inspect) 
  (cedille-mode-context) ;the string-split bug is here
  (cedille-mode-rebalance-windows))

					;UTILITY MACROS TO CUT DOWN ON NUMBER OF FUNCTIONS

(defmacro make-cedille-mode-buffer(buffer opt-fn minor-mode-fn jump-to-window-p require-selection-p)
  "Creates a function that can be used to toggle one of the buffers. Has five arguments:\n
1. The buffer\n
2. An optional function (without arguments) to be run/n
3. The minor mode associated with the buffer\n
4. A boolean indicating whether or not the cursor should automatically jump to the window.\n
5. A boolean indicating whether or not to require that a node be selected"
  `(lambda()
     (interactive)
     (let* ((buffer ,buffer)
	    (window (cedille-mode-toggle-buffer-display buffer)))            ;c.m.t.b.d returns the window (or nil)
       (when window                                                          ;if a window was created...
	 (if (or (not ,require-selection-p) se-mode-selected)                ;if selection requirements are met..
	     (progn
	       (,opt-fn)                                                     ;...run the optional function...
	       (with-current-buffer buffer (,minor-mode-fn))                 ;...enable minor mode in that window...
	       (when ,jump-to-window-p (select-window window)))              ;...and optionally jump to window
	   (cedille-mode-toggle-buffer-display buffer)                       ;..else we close the window and give an error message
	   (message "Error: must select a node"))))))

	   
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
      (setq json (sort json 'cedille-mode-compare-seqnums))
      (setq json (loop for (key . value) in json
                   collecting (cons key (cedille-mode-strip-seqnum value))))
      json))

(defun cedille-mode-initialize-span(span)
  "Initialize the given span read in by se-mode."
  (when span
    (se-new-span (se-span-name span) (se-span-start span) (se-span-end span)
      (cedille-mode-sort-and-strip-json (se-span-data span)))))


(defun cedille-mode-initialize-spans()
  "Initialize spans after they are read in by se-mode."
  (setq cedille-mode-highlight-spans (mapcar #'cedille-mode-initialize-span se-mode-spans))
  (setq se-mode-spans (remove-if
		       (lambda (span) (assoc 'not-for-navigation (se-span-data span)))
		       cedille-mode-highlight-spans)))


(defun cedille-mode-filter-out-special(data)
  "Filter out special attributes from the data in a span"
  (loop for (key . value) in data
        unless (or (eq key 'symbol) (eq key 'location) (eq key 'language-level) (eq key 'checking-mode)
                   (eq key 'summary) (eq key 'binder) (eq key 'keywords))
     collecting (cons key value)))

(defun cedille-mode-select-next(count)
  "Selects the next sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (when (> count 0)
    (se-mode-select-next)
    (cedille-mode-select-next (- count 1)))
  (cedille-mode-update-buffers)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defun cedille-mode-select-previous(count)
  "Selects the previous sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (when (> count 0)
	(se-mode-select-previous)
	(cedille-mode-select-previous (- count 1)))
  (cedille-mode-update-buffers)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defun cedille-mode-select-next-alt-test(x y)
  "Compares two spans x and y, testing whether x begins after y ends."
  (if (> (se-term-start y) (se-term-end x))
      t
      nil))

(defun cedille-mode-select-previous-alt-test(x y)
  (if (> (se-term-start x) (se-term-end y))
      t
      nil))

(defun cedille-mode-select-next-alt(count)
  "Selects the next sibling of the currently selected span, if one exists.
Otherwise, selects the first span beginning after the end of the current span,
Updates info buffer in either case"
  (interactive "p")
  (when (> count 0)
	(se-mode-set-spans)
	(unless (se-mode-select (se-mode-next))
	  (let ((found (cl-find (se-mode-selected) se-mode-spans :test #'cedille-mode-select-next-alt-test)))
	    (if (not found)
		(message "No next span")
	      (progn (cedille-mode-select-span found)))))
	(cedille-mode-select-next-alt (- count 1)))
  (cedille-mode-update-buffers))

(defun cedille-mode-select-previous-alt(count)
  "Selects the previous sibling of the currently selected node;
otherwise selects first span that ends before the current span begins.
Updates info buffer in either case."
  (interactive "p")
  (when (> count 0)
    (se-mode-set-spans)
    (unless (se-mode-select (se-mode-previous))
	(let ((found (cl-find (se-mode-selected) se-mode-spans
			:test #'cedille-mode-select-previous-alt-test
			:from-end t)))
	(if (not found)
	  (message "No previous span")
	  (cedille-mode-select-span found))))
    (cedille-mode-select-previous-alt (- count 1)))
    (cedille-mode-update-buffers)
)

(defun cedille-mode-select-parent(count)
  "Selects the parent of the currently selected node in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (if (> count 0)
      (progn
	(se-mode-expand-selected)
	(cedille-mode-select-parent (- count 1)))
    nil)
  (cedille-mode-update-buffers)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defun cedille-mode-select-first-child(count)
  "Selects the first child of the lowest node in the parse tree
containing point, and updates the Cedille info buffer."
  (interactive "p")
  (if (> count 0)
      (progn
	(se-mode-shrink-selected)
	(cedille-mode-select-first-child (- count 1)))
    nil)
  (cedille-mode-update-buffers)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defun cedille-mode-select-first()
  "Selects the first sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-first)
  (cedille-mode-update-buffers)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defun cedille-mode-select-last()
  "Selects the last sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-last)
  (cedille-mode-update-buffers)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defun cedille-mode-quit()
"Quit Cedille navigation mode"
(interactive)
(se-mode-clear-selected)
(remove-overlays)
(se-navigation-mode-quit)
(setq se-mode-parse-tree nil))

(defun cedille-mode-get-matching-variable-nodes(node)
  "Returns list of all nodes containing variables matching the one in the input node (if any). Matching is determined by location attribute"
  (let* ((rec-path-crawler (lambda (node rec-fn)
			     (let ((children (se-node-children node))
				   (output-list (list node)))
			       (if children
				   (dolist (child children output-list)
				     (setq output-list (append (funcall rec-fn child rec-fn) output-list)))
				 output-list))))
	 (path-start-node (car (se-find-span-path node (se-mode-parse-tree))))
	 (nodes-to-check (funcall rec-path-crawler path-start-node rec-path-crawler))
	 (data-selected (se-term-to-json node))
	 (location-selected (cdr (assoc 'location data-selected)))
	 (matching-nodes nil))
    (dolist (node nodes-to-check matching-nodes)
	  (let* ((data (se-term-to-json node))
		 (location (cdr (assoc 'location data))))
	    (when (equal location location-selected) (setq matching-nodes (cons node matching-nodes)))))))

(defun cedille-mode-highlight-occurrences()
  "Highlights all occurrences of bound variable matching selected node"
  (remove-overlays) ;delete all existing overlays
  (if se-mode-selected
      (let ((matching-nodes (cedille-mode-get-matching-variable-nodes (se-mode-selected))))
	(dolist (node matching-nodes)
	  (let* ((data (se-term-to-json node))
		 (symbol (cdr (assoc 'symbol data))) ; nodes without symbols should not be highlighted
		 (start (cdr (assoc 'start data)))
		 (end (cdr (assoc 'end data)))
		 (overlay (make-overlay start end)))
	    (when symbol
	      (overlay-put overlay 'face '(:background "white"))))))))
					 
(defun cedille-mode-restart-backend()
  "Restart cedille process"
  (interactive)
  (se-inf-stop)
  (se-inf-header-timer-stop)
  (se-inf-start (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS"))
  (message "Restarted cedille process"))

; se-navi-define-key maintains an association with the major mode,
; so that different major modes using se-navi-define-key can have
; separate keymaps.
(defun cedille-modify-keymap()
  (se-navi-define-key 'cedille-mode (kbd "f") #'cedille-mode-select-next)
  (se-navi-define-key 'cedille-mode (kbd "F") #'cedille-mode-select-next-alt)
  (se-navi-define-key 'cedille-mode (kbd "b") #'cedille-mode-select-previous)
  (se-navi-define-key 'cedille-mode (kbd "B") #'cedille-mode-select-previous-alt)
  (se-navi-define-key 'cedille-mode (kbd "p") #'cedille-mode-select-parent)
  (se-navi-define-key 'cedille-mode (kbd "n") #'cedille-mode-select-first-child)
  (se-navi-define-key 'cedille-mode (kbd "g") #'se-mode-clear-selected)
  (se-navi-define-key 'cedille-mode (kbd "q") #'cedille-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "M-s") #'cedille-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "C-g") #'cedille-mode-quit)
  (se-navi-define-key 'cedille-mode (kbd "e") #'cedille-mode-select-last)
  (se-navi-define-key 'cedille-mode (kbd "a") #'cedille-mode-select-first)
  (se-navi-define-key 'cedille-mode (kbd "i") (make-cedille-mode-buffer (cedille-mode-inspect-buffer) lambda cedille-inspect-view-mode nil t))
  (se-navi-define-key 'cedille-mode (kbd "I") (make-cedille-mode-buffer (cedille-mode-inspect-buffer) lambda cedille-inspect-view-mode t t))
  (se-navi-define-key 'cedille-mode (kbd "j") #'cedille-mode-jump)
  (se-navi-define-key 'cedille-mode (kbd ".") (make-cedille-mode-history-navigate t nil))
  (se-navi-define-key 'cedille-mode (kbd ",") (make-cedille-mode-history-navigate nil nil))
  (se-navi-define-key 'cedille-mode (kbd "<") (make-cedille-mode-history-navigate nil t))
  (se-navi-define-key 'cedille-mode (kbd ">") (make-cedille-mode-history-navigate t t))
  (se-navi-define-key 'cedille-mode (kbd "r") #'cedille-mode-select-next-error)
  (se-navi-define-key 'cedille-mode (kbd "R") #'cedille-mode-select-previous-error)
  (se-navi-define-key 'cedille-mode (kbd "t") #'cedille-mode-select-first-error-in-file)
  (se-navi-define-key 'cedille-mode (kbd "T") #'cedille-mode-select-last-error-in-file)
  (se-navi-define-key 'cedille-mode (kbd "c") (make-cedille-mode-buffer (cedille-mode-context-buffer) cedille-mode-context cedille-context-view-mode nil t))
  (se-navi-define-key 'cedille-mode (kbd "C") (make-cedille-mode-buffer (cedille-mode-context-buffer) cedille-mode-context cedille-context-view-mode t t))
  (se-navi-define-key 'cedille-mode (kbd "K") #'cedille-mode-restart-backend)
  (se-navi-define-key 'cedille-mode (kbd "s") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode nil nil))
  (se-navi-define-key 'cedille-mode (kbd "S") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode t nil))
  (se-navi-define-key 'cedille-mode (kbd "h") (make-cedille-mode-info-display-page nil))
  (se-navi-define-key 'cedille-mode (kbd "C-h 1") #'cedille-mode-highlight-default)
  (se-navi-define-key 'cedille-mode (kbd "C-h 2") #'cedille-mode-highlight-language-level)
  (se-navi-define-key 'cedille-mode (kbd "C-h 3") #'cedille-mode-highlight-checking-mode)
  (se-navi-define-key 'cedille-mode (kbd "$") (make-cedille-mode-customize "cedille"))
  (se-navi-define-key 'cedille-mode (kbd "1") #'delete-other-windows)
)

(cedille-modify-keymap)

(se-create-mode "cedille" nil
  "Major mode for Cedille files."

  (setq-local comment-start "%")
  
  (se-inf-start
   (or (get-buffer-process "*cedille-mode*") ;; reuse if existing process
       (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS")))

  (set-input-method "Cedille")
)

(define-key cedille-mode-map (kbd "M-s") #'cedille-start-navigation)

(defun cedille-start-navigation()
  "Enter Cedille navigation mode."
  (interactive)
  (setq se-mode-parse-tree nil)
  (se-navigation-mode 1))     

(add-hook 'se-inf-response-hook 'cedille-mode-set-error-spans t)
(add-hook 'se-inf-init-spans-hook 'cedille-mode-initialize-spans t)
(add-hook 'se-inf-init-spans-hook 'cedille-mode-highlight-default t)

(modify-coding-system-alist 'file "\\.ced\\'" 'utf-8)

(quail-define-package "Cedille" "UTF-8" "δ" t ; guidance
		      "Cedille input method."
		      nil nil nil nil nil nil t) ; maximum-shortest

(mapc (lambda (pair) (quail-defrule (car pair) (cadr pair) "Cedille"))
	'(("\\l" "λ") ("\\L" "Λ") ("\\>" "→") ("\\r" "→") ("\\a" "∀") ("\\B" "□") ("\\P" "Π") 
          ("\\s" "★") ("\\S" "☆") ("\\." "·") ("\\f" "⇐") ("\\<" "⇐") ("\\u" "↑") ("\\p" "π")
          ("\\h" "●") ("\\k" "𝒌") ("\\i" "ι") ("\\=" "≃") ("\\d" "δ") 
          ("\\b" "β") ("\\e" "ε") ("\\R" "ρ") ("\\y" "ς") ("\\t" "θ") ("\\x" "χ")

          ("\\rho" "ρ") ("\\theta" "θ") ("\\epsilon" "ε") ; add some more of these
 ))

(provide 'cedille-mode)
;;; cedille-mode.el ends here

