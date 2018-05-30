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
(setq max-lisp-eval-depth 30000
      max-specpdl-size 50000)

(defvar cedille-mode-browsing-history '(nil nil)) ;stores history while jumping between files

(make-variable-buffer-local
 (defvar cedille-mode-do-update-buffers t
   "A boolean for whether `cedille-mode-update-buffers' should get called"))

(autoload 'cedille-mode "cedille-mode" "Major mode for editing cedille files ." t)
(add-to-list 'auto-mode-alist (cons "\\.ced\\'" 'cedille-mode))

(let ((se-path (concat cedille-path "/se-mode")))
  (add-to-list 'load-path se-path)
  (add-to-list 'load-path (concat se-path "/json.el")))
(require 'se)

(let ((cedille-mode-library-path (concat cedille-path "/cedille-mode")))
  (add-to-list 'load-path cedille-mode-library-path)
  (add-to-list 'load-path (concat cedille-mode-library-path "/json.el")))
(require 'cedille-mode-library)

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
(require 'se-markup)
;(require 'se-thread)
(eval-when-compile (require 'se-macros))

(defvar cedille-mode-version "1.0"
  "The version of the cedille mode.")

(setq se-inf-parsing-header "Parsing")

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

(defcustom cedille-mode-autohighlight-color "dark gray"
  "Determines the color (background) of highlighting for the autohighlight matching variables feature"
  :type '(color)
  :group 'cedille)

(defcustom cedille-mode-wrap-navigation nil
  "Wrap navigation"
  :type '(boolean)
  :group 'cedille)

;; ----------------------------------------------------------------------------



(defvar cedille-mode-highlight-spans nil
  "Spans including spans marked not-for-navigation.")


					; UTILITY FUNCTIONS FOR MANAGING WINDOWS

(defun cedille-mode-get-create-window(&optional buffer)
  "Retrieves the window associated with the given buffer or else creates a new window and fills it with the buffer"
  (let ((window (get-buffer-window buffer)))
    (unless window
      (let ((sw (selected-window)))
	(setq window (split-window (selected-window))))
      (set-window-buffer window (or buffer (buffer-name)))
      (cedille-mode-rebalance-windows))
    window))

(defun cedille-mode-toggle-buffer-display(buffer)
  "Toggles display of buffer on or off. Returns nil if window was deleted, or the window if it was created."
  (let ((window (get-buffer-window buffer)))
    (if (null window)
	(let ((window (cedille-mode-get-create-window buffer)))
	  (setq window-size-fixed nil)
	  (cedille-mode-rebalance-windows)
	  window)
      (delete-window window)
      (cedille-mode-rebalance-windows))))

(defun cedille-mode-rebalance-windows()
  "Resizes all windows"
  (let* ((fws-nfws (cedille-mode-file-windows))
         (pred (lambda (w1 w2) (< (cadr (window-edges w1)) (cadr (window-edges w2)))))
         (fws (sort (car fws-nfws) pred))
         (nfws (sort (cdr fws-nfws) pred)))
    (loop for w in nfws do
          (with-selected-window w
            (with-current-buffer (window-buffer)
              (let ((window-size-fixed nil))
                (fit-window-to-buffer w))
              (setq window-size-fixed t))))
    (let ((mean (cedille-mode-mean-window-size fws)))
      (loop for w in fws do
            (with-selected-window w
              (with-current-buffer (window-buffer)
                (let* ((window-size-fixed nil)
                       (mean2 (max mean (window-min-size))))
                  (fit-window-to-buffer w mean2 mean2))))))
    (loop for w in nfws do
          (with-selected-window w
            (with-current-buffer (window-buffer)
              (setq window-size-fixed nil))))))

(defun cedille-mode-rebalance-windows-old()
  (walk-windows #'fit-window-to-buffer))

(defun cedille-mode-file-windows ()
  "Returns (cons FILE-WINDOWS NOT-FILE-WINDOWS)"
  (let (fw nfw)
    (walk-windows (lambda (window)
		    (if (buffer-file-name (window-buffer window))
			(push window fw)
		      (push window nfw))))
    (cons fw nfw)))

(defun cedille-mode-mean-window-size (windows)
  "Calculates the mean size of WINDOWS"
  (round (/ (cedille-mode-mean-window-size-h windows 0) (float (length windows)))))

(defun cedille-mode-mean-window-size-h (windows size)
  "Helper for `cedille-mode-mean-window-size'"
  (if (null windows) size
    (cedille-mode-mean-window-size-h (cdr windows) (+ size (window-height (car windows))))))

(defun cedille-mode-set-windows-height (windows height)
  "Sets each window in WINDOWS to be HEIGHT lines high"
  (when windows
    (let* ((window (car windows))
	   (height (max height (window-min-size window))))
      (window-resize window (- height (window-body-size window))))
    (cedille-mode-set-windows-height (cdr windows) height)))

(defun cedille-mode-split-window ()
  (interactive)
  (split-window))

(defun cedille-mode-close-active-window() (interactive) (delete-window))

					;UTILITY FUNCTIONS FOR MANAGING BUFFERS

(defun cedille-mode-update-buffers()
  "Update the info and context buffers."
  (when cedille-mode-do-update-buffers
    (cedille-mode-inspect) 
    (cedille-mode-context) ;the string-split bug is here
    (cedille-mode-rebalance-windows)))

(defun cedille-mode-clear-buffers()
  "Clears the contents of and closes the buffers for the current file"
  (cedille-mode-clear-buffer (cedille-mode-inspect-buffer-name))
  (cedille-mode-clear-buffer (cedille-mode-context-buffer-name))
  (cedille-mode-clear-buffer (cedille-mode-summary-buffer-name)))

(defun cedille-mode-clear-buffer(buffer)
  "Clears the contents of and closes BUFFER"
  (when (get-buffer buffer)
    (select-window (get-buffer-window))
    (with-current-buffer buffer
      (let ((window (get-buffer-window buffer)))
	(let ((buffer-read-only nil))
	  (erase-buffer))
	(when window
	  (delete-window (get-buffer-window buffer)))))))

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
  (let ((na (cadr a))
        (nb (cadr b)))
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
      (setq json (loop for kv in json
                   collecting (cedille-mode-apply-tag kv)))
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
                   (eq key 'summary) (eq key 'binder) (eq key 'bound-value) (eq key 'keywords) (eq key 'erasure))
     collecting (cons key value)))

(defun cedille-mode-select-next(count)
  "Selects the next sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (when (> count 0)
    (se-mode-select-next cedille-mode-wrap-navigation)
    (cedille-mode-select-next (- count 1)))
  (cedille-mode-update-buffers)
  (cedille-mode-highlight-occurrences-if))

(defun cedille-mode-select-previous(count)
  "Selects the previous sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (when (> count 0)
    (se-mode-select-previous cedille-mode-wrap-navigation)
    (cedille-mode-select-previous (- count 1)))
  (cedille-mode-update-buffers)
  (cedille-mode-highlight-occurrences-if))

(defun cedille-mode-select-next-alt-test(x y)
  "Compares two spans x and y, testing whether x begins after y ends."
  (> (se-term-start y) (se-term-end x)))

(defun cedille-mode-select-previous-alt-test(x y)
  (> (se-term-start x) (se-term-end y)))

(defun cedille-mode-select-next-alt (count)
  "Selects the next sibling of the currently selected span, if one exists.
Otherwise, selects the first span beginning after the end of the current span,
Updates info buffer in either case"
  (interactive "p")
  (when (and (> count 0) se-mode-selected)
    (se-mode-set-spans)
    (unless (se-mode-select (se-mode-next))
      (setq found (cl-find (se-mode-selected) se-mode-spans :test #'cedille-mode-select-next-alt-test))
      (if found
	  (cedille-mode-select-span found)
	(if cedille-mode-wrap-navigation
	    (let ((inhibit-message t))
	      (se-mode-select (se-mode-left-spine (car (se-mode-parse-tree))))
	      (cedille-mode-select-first-child 1))
	  (message "No next span"))))
    (cedille-mode-select-next-alt (- count 1)))
  (cedille-mode-update-buffers))

(defun cedille-mode-select-previous-alt (count)
  "Selects the previous sibling of the currently selected node;
otherwise selects first span that ends before the current span begins.
Updates info buffer in either case."
  (interactive "p")
  (when (and (> count 0) se-mode-selected)
    (se-mode-set-spans)
    (setq continue t)
    (unless (se-mode-select (se-mode-previous))
      (setq found (cl-find (se-mode-selected) se-mode-spans :test #'cedille-mode-select-previous-alt-test :from-end t))
      (if found
	  (cedille-mode-select-span found)
	(if cedille-mode-wrap-navigation
	    (let ((inhibit-message t))
	      (se-mode-select (se-last-span (se-mode-parse-tree)))
	      (cedille-mode-select-first-child 1))
	  (message "No previous span"))))
    (cedille-mode-select-previous-alt (- count 1)))
  (cedille-mode-update-buffers))

(defun cedille-mode-select-parent(count)
  "Selects the parent of the currently selected node in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (when (> count 0)
    (se-mode-expand-selected)
    (cedille-mode-select-parent (- count 1)))
  (cedille-mode-update-buffers)
  (cedille-mode-highlight-occurrences-if))

(defun cedille-mode-select-first-child(count)
  "Selects the first child of the lowest node in the parse tree
containing point, and updates the Cedille info buffer."
  (interactive "p")
  (when (> count 0)
    (se-mode-shrink-selected)
    (cedille-mode-select-first-child (- count 1)))
  (cedille-mode-update-buffers)
  (cedille-mode-highlight-occurrences-if))

(defun cedille-mode-select-first()
  "Selects the first sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-first)
  (cedille-mode-update-buffers)
  (cedille-mode-highlight-occurrences-if))

(defun cedille-mode-select-last()
  "Selects the last sibling of the currently selected node
in the parse tree, and updates the Cedille info buffer."
  (interactive)
  (se-mode-select-last)
  (cedille-mode-update-buffers)
  (cedille-mode-highlight-occurrences-if))

;(defun cedille-mode-modify-response (response)
;  (replace-regexp-in-string "^ +"  "" response))

(defun cedille-mode-quit()
  "Quit Cedille navigation mode"
  (interactive)
  (se-mode-clear-selected)
  (remove-overlays)
  (se-navigation-mode-quit)
  (setq se-mode-parse-tree nil
	cedille-mode-error-spans nil))

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
    (when (not (equal location-selected "missing - missing")) ;Don't match nodes with no location
      (dolist (node nodes-to-check matching-nodes)
	(let* ((data (se-term-to-json node))
	       (location (cdr (assoc 'location data))))
	  (when (equal location location-selected) (setq matching-nodes (cons node matching-nodes))))))))

(defun cedille-mode-replace-occurrences(new-label)
  "Replaces all occurrences of bound variable matching selected node with input label"
  (interactive "sRename as: ")
  (when se-mode-selected
    (let* ((order-p (lambda (a b)
		      (let* ((data-a (se-term-to-json a))
			     (data-b (se-term-to-json b))
			     (start-a (cdr (assoc 'start data-a)))
			     (start-b (cdr (assoc 'start data-b))))
			(> start-a start-b))))
	   (matching-nodes (cedille-mode-get-matching-variable-nodes (se-mode-selected)))
	   (sorted-nodes (sort matching-nodes order-p))) ; order the nodes in descending order by position in file
      (dolist (node sorted-nodes)
	(let* ((data (se-term-to-json node))
	       (symbol (cdr (assoc 'symbol data))) ; nodes without symbols should not be checked
	       (start (cdr (assoc 'start data)))
	       (end (cdr (assoc 'end data))))
	  (when symbol
	    (save-excursion
	      (delete-region start end)
	      (goto-char start)
	      (insert new-label))))))))

(defun cedille-mode-highlight-occurrences()
  "Highlights all occurrences of bound variable matching selected node and returns list of nodes"
  (remove-overlays) ;delete all existing overlays
  (cedille-mode-highlight-error-overlay cedille-mode-error-spans)
  (if se-mode-selected
      (let ((matching-nodes (cedille-mode-get-matching-variable-nodes (se-mode-selected))))
	(dolist (node matching-nodes)
	  (let* ((data (se-term-to-json node))
		 (symbol (cdr (assoc 'symbol data))) ; nodes without symbols should not be highlighted
		 (start (cdr (assoc 'start data)))
		 (end (cdr (assoc 'end data)))
		 (overlay (make-overlay start end)))
	    (when symbol
	      (overlay-put overlay 'face `(:background ,cedille-mode-autohighlight-color)))))
	matching-nodes)))

(defun cedille-mode-highlight-occurrences-if()
  "If the option is set to highlight matching variable 
occurrences, then do so."
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(defvar cedille-mode-matching-nodes nil)

(defun cedille-mode-interactive-highlight()
  "Interactive command to call cedille-mode-highlight-occurences"
  (interactive)
  (let ((matching-nodes (cedille-mode-highlight-occurrences)))
    (if (equal cedille-mode-matching-nodes matching-nodes)
	(progn
	  (remove-overlays)
          (cedille-mode-highlight-error-overlay cedille-mode-error-spans)
	  (setq cedille-mode-matching-nodes nil))
      (setq cedille-mode-matching-nodes matching-nodes))))

(defun cedille-mode-apply-tags (str tags)
  "Helper for `cedille-mode-apply-tag'"
  (if (null tags)
      str
    (let* ((tag (car tags))
           (tail (cdr tags))
           (start (string-to-number (cdr (assoc 'start (cdr tag)))))
           (end (string-to-number (cdr (assoc 'end (cdr tag)))))
           (data (cdr tag))
           (symbol (car tag)))
      (cedille-mode-apply-tags (se-pin-data start end symbol data str) tail))))

(defun cedille-mode-apply-tag (tag)
  "Applies the tags in TAG to its value"
  (let* ((len (length (format "%s" tag)))
        (key (car tag))
        (value (caddr tag))
        (tags (cadddr tag))
        (ret (cons key (cedille-mode-apply-tags value tags))))
    ret))

(defun cedille-mode-elaborate(dir)
  "Elaborates the current file"
  (interactive "GElaboration output: ")
  (let ((dir2 (expand-file-name dir)))
    (se-inf-interactive (concat "elaborate" sep (buffer-file-name) sep dir2)
      (lambda (response extra)
        (let ((num (string-to-number response)))
          (if (zerop num)
              (with-current-buffer (car extra)
                (with-selected-window (cedille-mode-split-window)
                  (with-current-buffer (window-buffer)
                    (message "Elaboration complete")
                    (find-file (cdr extra)))))
            (message "Elaboration error (code %d)" num))))
      (cons (current-buffer) dir2) :header "Elaborating")))

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
(defun cedille-modify-keymap(mode)
  (se-navi-define-key mode (kbd "f") #'cedille-mode-select-next)
  (se-navi-define-key mode (kbd "F") #'cedille-mode-select-next-alt)
  (se-navi-define-key mode (kbd "b") #'cedille-mode-select-previous)
  (se-navi-define-key mode (kbd "B") #'cedille-mode-select-previous-alt)
  (se-navi-define-key mode (kbd "p") #'cedille-mode-select-parent)
  (se-navi-define-key mode (kbd "n") #'cedille-mode-select-first-child)
  (se-navi-define-key mode (kbd "m") #'cedille-mode-interactive-highlight)
  (se-navi-define-key mode (kbd "g") #'se-mode-clear-selected)
  (se-navi-define-key mode (kbd "q") #'cedille-mode-quit)
  (se-navi-define-key mode (kbd "M-s") #'cedille-mode-quit)
  (se-navi-define-key mode (kbd "C-g") #'cedille-mode-quit)
  (se-navi-define-key mode (kbd "e") #'cedille-mode-select-last)
  (se-navi-define-key mode (kbd "a") #'cedille-mode-select-first)
  (se-navi-define-key mode (kbd "i") (make-cedille-mode-buffer (cedille-mode-inspect-buffer) lambda cedille-mode-inspect nil t))
  (se-navi-define-key mode (kbd "I") (make-cedille-mode-buffer (cedille-mode-inspect-buffer) lambda cedille-mode-inspect t t))
  (se-navi-define-key mode (kbd "j") #'cedille-mode-jump)
  (se-navi-define-key mode (kbd "=") #'cedille-mode-replace-occurrences)
  (se-navi-define-key mode (kbd ".") (make-cedille-mode-history-navigate t nil))
  (se-navi-define-key mode (kbd ",") (make-cedille-mode-history-navigate nil nil))
  (se-navi-define-key mode (kbd "<") (make-cedille-mode-history-navigate nil t))
  (se-navi-define-key mode (kbd ">") (make-cedille-mode-history-navigate t t))
  (se-navi-define-key mode (kbd "r") #'cedille-mode-select-next-error)
  (se-navi-define-key mode (kbd "R") #'cedille-mode-select-previous-error)
  (se-navi-define-key mode (kbd "t") #'cedille-mode-select-first-error-in-file)
  (se-navi-define-key mode (kbd "T") #'cedille-mode-select-last-error-in-file)
  (se-navi-define-key mode (kbd "c") (make-cedille-mode-buffer (cedille-mode-context-buffer) cedille-mode-context cedille-context-view-mode nil t))
  (se-navi-define-key mode (kbd "C") (make-cedille-mode-buffer (cedille-mode-context-buffer) cedille-mode-context cedille-context-view-mode t t))
  (se-navi-define-key mode (kbd "K") #'cedille-mode-restart-backend)
  (se-navi-define-key mode (kbd "s") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode nil nil))
  (se-navi-define-key mode (kbd "S") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode t nil))
  (se-navi-define-key mode (kbd "h") (make-cedille-mode-info-display-page nil))
  (se-navi-define-key mode (kbd "E") #'cedille-mode-elaborate)
  (se-navi-define-key mode (kbd "C-h 1") #'cedille-mode-highlight-default)
  (se-navi-define-key mode (kbd "C-h 2") #'cedille-mode-highlight-language-level)
  (se-navi-define-key mode (kbd "C-h 3") #'cedille-mode-highlight-checking-mode)
  (se-navi-define-key mode (kbd "$") (make-cedille-mode-customize "cedille"))
  (se-navi-define-key mode (kbd "1") #'delete-other-windows)
  (se-navi-define-key mode (kbd "P") (lambda () (interactive) (message "se-mode-selected: %s" (se-mode-selected))))
  (se-navi-define-key mode (kbd "?") #'cedille-mode-backend-debug)
  (se-navi-define-key mode (kbd "x") #'cedille-mode-scratch-toggle)
  (se-navi-define-key mode (kbd "X") (lambda () (interactive) (cedille-mode-scratch-toggle t)))
  ;(se-navi-define-key mode (kbd "y") #'cedille-mode-br-toggle)
  ;(se-navi-define-key mode (kbd "Y") (lambda () (interactive) (cedille-mode-br-toggle t)))
  (se-navi-define-key mode (kbd "M-c") #'cedille-mode-scratch-copy-span)
  (se-navi-define-key mode (kbd "+") (make-cedille-mode-resize-current-window 1))
  (se-navi-define-key mode (kbd "-") (make-cedille-mode-resize-current-window -1))
  (se-navi-define-key mode (kbd "=") #'cedille-mode-unlock-current-window-size)
  (se-navi-define-key mode (kbd "C-x 2") #'cedille-mode-split-window)
  ; Interactive commands
  (se-navi-define-key mode (kbd "C-i h") (lambda () (interactive) (cedille-mode-normalize t)))
  (se-navi-define-key mode (kbd "C-i n") #'cedille-mode-normalize)
  (se-navi-define-key mode (kbd "C-i e") #'cedille-mode-erase)
  (se-navi-define-key mode (kbd "C-i b") #'cedille-mode-br)
  (se-navi-define-key mode (kbd "C-i B") #'cedille-mode-br-node)
  (se-navi-define-key mode (kbd "C-i t") #'cedille-mode-br-type)
  (se-navi-define-key mode (kbd "C-i =") #'cedille-mode-conv)
  (se-navi-define-key mode (kbd "C-i s") #'cedille-mode-to-string)
  ;(se-navi-define-key mode (kbd "C-i d") #'cedille-mode-inspect-clear)
  (se-navi-define-key mode (kbd "C-i r") #'cedille-mode-inspect-clear)
  ;(se-navi-define-key mode (kbd "C-i D") #'cedille-mode-inspect-clear-all)
  (se-navi-define-key mode (kbd "C-i R") #'cedille-mode-inspect-clear-all)
;  (se-navi-define-key 'cedille-mode (kbd "@") #'cedille-mode-find)
)
(require 'cedille-mode-beta-reduce)

(cedille-modify-keymap 'cedille-mode)

(defun cedille-mode-get-message-from-filename(filename)
  "Get the message to send to the backend, from the name of the file to parse."
  (concat "check§" filename))

(defun cedille-mode-progress-fn (response &optional oc buffer span)
  "The function called when a progress update is received from the backend"
  (se-inf-queue-header response)
  (se-inf-next-header)
  "progress stub")

(se-create-mode "cedille" nil
  "Major mode for Cedille files."

  (setq-local comment-start "--")

  (se-inf-start (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS"))
  ;;(or (get-buffer-process "*cedille-mode*") ;; reuse if existing process
    ;;   (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS")))
  (add-hook 'se-inf-init-spans-hook 'cedille-mode-set-error-spans t)
  (add-hook 'se-inf-init-spans-hook 'cedille-mode-initialize-spans t)
  ;(add-hook 'se-inf-init-spans-hook 'se-markup-propertize-spans t)
  (add-hook 'se-inf-init-spans-hook 'cedille-mode-highlight-default t)
  (add-hook 'se-inf-pre-parse-hook 'cedille-mode-clear-buffers)
  (add-hook 'deactivate-mark-hook 'cedille-mode-highlight-occurrences)

  (setq-local se-inf-get-message-from-filename 'cedille-mode-get-message-from-filename)
  (setq-local se-inf-progress-fn 'cedille-mode-progress-fn)
  (setq-local se-inf-progress-prefix "progress: ")
  ;(setq-local se-inf-modify-response 'cedille-mode-modify-response)

  (set-input-method "Cedille")
)

(define-key cedille-mode-map (kbd "M-s") #'cedille-start-navigation)

(defun cedille-start-navigation()
  "Enter Cedille navigation mode."
  (interactive)
  (setq se-mode-parse-tree nil
        cedille-mode-parent-buffer (current-buffer))
  (se-navigation-mode 1))

(modify-coding-system-alist 'file "\\.ced\\'" 'utf-8)

(quail-define-package "Cedille" "UTF-8" "δ" t ; guidance
		      "Cedille input method."
		      nil nil nil nil nil nil t) ; maximum-shortest

(mapc (lambda (pair) (quail-defrule (car pair) (cadr pair) "Cedille"))
	'(("\\l" "λ") ("\\L" "Λ") ("\\>" "→") ("\\r" "➔") ("\\a" "∀") ("\\B" "□") ("\\P" "Π") 
          ("\\s" "★") ("\\S" "☆") ("\\." "·") ("\\f" "◂") ("\\u" "↑") ("\\p" "φ")
          ("\\h" "●") ("\\k" "𝒌") ("\\i" "ι") ("\\=" "≃") ("\\==" "≅") ("\\d" "δ") ("\\-" "➾")
          ("\\b" "β") ("\\e" "ε") ("\\R" "ρ") ("\\y" "ς") ("\\t" "θ") ("\\x" "χ") ("\\w" "ω")
          ("\\E" "∃") ("\\F" "φ")
          ("\\\\" "\\")

          ("\\rho" "ρ") ("\\theta" "θ") ("\\epsilon" "ε") ("\\phi" "φ"); add some more of these
 ))

(provide 'cedille-mode)
;;; cedille-mode.el ends here
