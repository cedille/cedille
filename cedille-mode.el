;;; cedille-mode.el --- Major mode for Cedille
;;;
;;; Only follow these instruction if you did NOT use the Debian package:
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
(eval-when-compile (require 'cl))

(setq max-lisp-eval-depth 30000
      max-specpdl-size 50000)

(defmacro cedille-platform-case (win osx unix dev)
  "If running on Windows, evaluate WIN; if OS X, OSX; otherwise, UNIX. If `cedille-path' is set, evaluate DEV instead."
  `(cond
    (,(boundp 'cedille-path) ,dev)
    (,(string= system-type "windows-nt") ,win)
    (,(string= system-type "darwin") ,osx)
    (t ,unix)))

(defvar cedille-program-name
  (cedille-platform-case
   "bin/cedille"
   nil
   "bin/cedille"
   (concat (file-name-as-directory cedille-path) "bin/cedille")))

(defvar cedille-core-program-name
  (cedille-platform-case
   "cedille-core"
   nil
   "cedille-core"
   (concat (file-name-as-directory (concat (file-name-as-directory cedille-path) "core")) "cedille-core")))


(defvar cedille-path-el
  (file-name-as-directory
   (cedille-platform-case
    "C:\\Program Files\\cedille"
    nil
    "/usr/share/emacs/site-lisp/cedille-mode"
    cedille-path)))

(defvar cedille-mode-browsing-history '(nil nil)) ;stores history while jumping between files

(make-variable-buffer-local
 (defvar cedille-mode-do-update-buffers t
   "A boolean for whether `cedille-mode-update-buffers' should get called"))

(make-variable-buffer-local
 (defvar cedille-mode-caching nil
   "Whether or not the backend is still writing .cede files"))

(make-variable-buffer-local
 (defvar cedille-mode-caching-queued nil
   "Whether or not the caching header has been queued"))

(make-variable-buffer-local
 (defvar cedille-mode-print-caching-finished nil
   "Whether or not to print when Cedille has finished writing .cede files"))

(defvar cedille-mode-progress-msg "progress stub")
(defvar cedille-mode-status-msg "status ping")
(defvar cedille-mode-progress-prefix "progress: ")
(defvar cedille-mode-caching-header "Caching")
(defvar cedille-mode-sep "§")

(autoload 'cedille-mode "cedille-mode" "Major mode for editing cedille files ." t)
(add-to-list 'auto-mode-alist (cons "\\.ced\\'" 'cedille-mode))

(let ((se-path (file-name-as-directory (concat cedille-path-el "se-mode"))))
  (add-to-list 'load-path se-path)
  (add-to-list 'load-path (concat se-path "json.el")))

(let ((cedille-mode-library-path (file-name-as-directory (concat cedille-path-el "cedille-mode"))))
  (add-to-list 'load-path cedille-mode-library-path)
  (add-to-list 'load-path (concat cedille-mode-library-path "json.el")))

(require 'se)
(require 'cedille-mode-library)

(defun cedille-mode-current-buffer-base-name()
    "A helper function to get the current buffer name without any extension"
    (file-name-sans-extension (buffer-name (current-buffer))))

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
    (cedille-mode-context)
    (cedille-mode-meta-vars)
    (cedille-mode-rebalance-windows)))

(defun cedille-mode-clear-buffers()
  "Clears the contents of and closes the buffers for the current file"
  (cedille-mode-clear-buffer (cedille-mode-inspect-buffer-name))
  (cedille-mode-clear-buffer (cedille-mode-context-buffer-name))
  (cedille-mode-clear-buffer (cedille-mode-meta-vars-buffer-name))
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

(defmacro with-cedille-buffer(no-revert-window-p &rest body)
  "Executes BODY inside the cedille buffer, reverting to whatever initial window was selected unless no-revert-window-p is non-nil."
  (declare (indent 1) (debug t))
  `(let ((window (get-buffer-window)))
     (if (null cedille-mode-parent-buffer)
         (error "Not a cedille buffer")
       (let ((ret (with-current-buffer cedille-mode-parent-buffer
                    (select-window (get-buffer-window) t)
                    ,@body)))
         (unless ,no-revert-window-p
           (select-window window))
         ret))))

(defmacro make-cedille-mode-buffer(buffer opt-fn minor-mode-fn jump-to-window-p require-selection-p)
  "Creates a function that can be used to toggle one of the buffers. Has five arguments:\n
1. The buffer\n
2. An optional function (without arguments) to be run/n
3. The minor mode associated with the buffer\n
4. A boolean indicating whether or not the cursor should automatically jump to the window.\n
5. A boolean indicating whether or not to require that a node be selected"
  `(lambda()
     (interactive)
     (with-cedille-buffer ,jump-to-window-p
         (let* ((buffer ,buffer)
                (window (cedille-mode-toggle-buffer-display buffer)))            ;c.m.t.b.d returns the window (or nil)
           (when window                                                          ;if a window was created...
             (if (or (not ,require-selection-p) se-mode-selected)                ;if selection requirements are met..
                 (progn
                   (,opt-fn)                                                     ;...run the optional function...
                   (with-current-buffer buffer (,minor-mode-fn))                 ;...enable minor mode in that window...
                   (when ,jump-to-window-p (select-window window)))              ;...and optionally jump to window
               (cedille-mode-toggle-buffer-display buffer)                       ;..else we close the window and give an error message
               (message "Error: must select a node")))
           (cedille-mode-update-buffers)))))

(defun cedille-mode-concat-sep (&rest seqs)
  "Concatenates STRS with cedille-mode-sep between each"
  (when seqs (concat (car seqs) (se-foldr (cdr seqs) "" (lambda (h x) (concat cedille-mode-sep h x))))))
	   
(defun cedille-mode-concat-sep2(sep ss)
  "Concat the strings in nonempty list ss with sep in between each one."
  (let ((he (car ss))
        (ta (cdr ss)))
    (if (not ta) he
      (concat he sep (cedille-mode-concat-sep2 sep ta)))))

(defun cedille-mode-set-assoc-value (alist key new-value)
  "Sets the value of 'KEY in ALIST to NEW-VALUE, or adds it if there was none"
  (append (assq-delete-all key alist) (list (cons key new-value))))

(defun cedille-mode-split-string(s)
  "Return a pair of the prefix of the string up to the first space, 
and the remaining suffix."
  (let ((ss (split-string s " ")))
    (if (< (length ss) 2) s
      (cons (car ss) (cedille-mode-concat-sep2 " " (cdr ss))))))


;(defun cedille-mode-get-seqnum(a)
;  "Get the seqnum from a json pair. The second component
;is assumed to be a string with a sequence number (prefix up
; to the first space in each string)."
;  (car (cedille-mode-split-string (cdr a))))

;(defun cedille-mode-compare-seqnums(a b)
;  "Compare two pairs by seqnum."
;  (let ((na (cadr a))
;        (nb (cadr b)))
;      (< (string-to-number na) (string-to-number nb))))

;(defun cedille-mode-strip-seqnum(s)
;  "Return a new string just like s except without the prefix up to the 
;first space."
;  (cdr (cedille-mode-split-string s)))

(defun cedille-mode-sort-and-strip-json(json)
  "Sort the pairs in the JSON data by the number at the 
start of each string, and then strip out that number."
  (when json
      ;(setq json (sort json 'cedille-mode-compare-seqnums))
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
		       cedille-mode-highlight-spans))
  (cedille-mode-matching-nodes-init))

 ;; [[file:src/spans.agda::special-tags%20:%20%F0%9D%95%83%20string][Backend]]
(defun cedille-mode-filter-out-special(data)
  "Filter out special attributes from the data in a span"
  (loop for (key . value) in data
        unless (or (eq key 'symbol) (eq key 'location) (eq key 'language-level) (eq key 'checking-mode)
                   (eq key 'summary) (eq key 'binder) (eq key 'bound-value) (eq key 'keywords) (eq key 'fileid) (eq key 'meta-vars-intro) (eq key 'meta-vars-sol) (eq key 'meta-var-locale))
        collecting (cons key value)))

(defun cedille-mode-select-next(count)
  "Selects the next sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (if (> count 0)
      (progn
        (se-mode-select-next cedille-mode-wrap-navigation)
        (cedille-mode-select-next (- count 1)))
    (cedille-mode-update-buffers)
    (cedille-mode-highlight-occurrences-if)))

(defun cedille-mode-select-previous(count)
  "Selects the previous sibling from the currently selected one in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (if (> count 0)
      (progn
        (se-mode-select-previous cedille-mode-wrap-navigation)
        (cedille-mode-select-previous (- count 1)))
    (cedille-mode-update-buffers)
    (cedille-mode-highlight-occurrences-if)))

(defun cedille-mode-select-previous-alt-better (s0 s1 s2)
  (if (< (se-term-start s0) (se-term-end s2)) s1
    (if (or (null s1)
            (cedille-mode-term-inside s2 s1)
            (cedille-mode-term-before s1 s2))
        s2 s1)))

(defun cedille-mode-term-inside(in out)
  (and (<= (se-term-start out) (se-term-start in))
       (>= (se-term-end   out) (se-term-end   in))))

(defun cedille-mode-term-before(before after)
  (<= (se-term-end before) (se-term-start after)))

(defun cedille-mode-select-next-alt-better (s0 s1 s2)
  (if (> (se-term-end s0) (se-term-start s2)) s1
    (if (or (null s1)
            (cedille-mode-term-inside s2 s1)
            (cedille-mode-term-before s2 s1))
        s2 s1)))

(defun cedille-mode-select-previous-alt-find (orig best spans)
  (if (null spans)
      best
    (cedille-mode-select-previous-alt-find orig
     (cedille-mode-select-previous-alt-better orig best (car spans)) (cdr spans))))

(defun cedille-mode-select-next-alt-find (orig best spans)
  (if (null spans)
      best
    (cedille-mode-select-next-alt-find orig
     (cedille-mode-select-next-alt-better orig best (car spans)) (cdr spans))))

(defun cedille-mode-select-next-alt (count)
  "Selects the next sibling of the currently selected span, if one exists.
Otherwise, selects the first span beginning after the end of the current span,
Updates info buffer in either case"
  (interactive "p")
  (when (and (> count 0) se-mode-selected)
    (se-mode-set-spans)
    (setq found (cedille-mode-select-next-alt-find (se-mode-selected) nil se-mode-spans))
    (if found
        (progn
          (se-mode-select found)
          (cedille-mode-update-buffers)
          (cedille-mode-highlight-occurrences-if))
      (if cedille-mode-wrap-navigation
          (let ((inhibit-message t))
            (se-mode-select (se-mode-left-spine (car (se-mode-parse-tree))))
            (cedille-mode-select-first-child 1))
        (message "No next span")))
    (cedille-mode-select-next-alt (- count 1))))

(defun cedille-mode-select-previous-alt (count)
  "Selects the previous sibling of the currently selected node;
otherwise selects first span that ends before the current span begins.
Updates info buffer in either case."
  (interactive "p")
  (when (and (> count 0) se-mode-selected)
    (se-mode-set-spans)
    (setq found (cedille-mode-select-previous-alt-find (se-mode-selected) nil se-mode-spans))
    (if found
        (progn
          (se-mode-select found)
          (cedille-mode-update-buffers)
          (cedille-mode-highlight-occurrences-if))
      (if cedille-mode-wrap-navigation
          (let ((inhibit-message t))
            (se-mode-select (se-last-span (se-mode-parse-tree)))
            (cedille-mode-select-first-child 1))
        (message "No previous span")))
    (cedille-mode-select-previous-alt (- count 1))))

(defun cedille-mode-select-parent(count)
  "Selects the parent of the currently selected node in 
the parse tree, and updates the Cedille info buffer."
  (interactive "p")
  (if (> count 0)
      (progn
        (se-mode-expand-selected)
        (cedille-mode-select-parent (- count 1)))
    (cedille-mode-update-buffers)
    (cedille-mode-highlight-occurrences-if)))

(defun cedille-mode-select-first-child(count)
  "Selects the first child of the lowest node in the parse tree
containing point, and updates the Cedille info buffer."
  (interactive "p")
  (if (> count 0)
    (progn
      (se-mode-shrink-selected)
      (cedille-mode-select-first-child (- count 1)))
    (cedille-mode-update-buffers)
    (cedille-mode-highlight-occurrences-if)))

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

(defun cedille-mode-quit-keep-mark()
  "Quit Cedille navigation mode"
  (interactive)
  (cedille-mode-quit)
  (setq mark-active t))

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
	 (data-selected (se-term-data node))
	 (location-selected (cdr (assoc 'location data-selected)))
	 (matching-nodes nil))
    (when (and location-selected (not (equal location-selected "missing - missing"))) ;Don't match nodes with no location (or missing one)
      (dolist (node nodes-to-check matching-nodes)
	(let* ((data (se-term-data node))
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

(defun cedille-mode-highlight-occurrences-if()
  "If the option is set to highlight matching variable 
occurrences, then do so."
  (cedille-mode-clear-interactive-highlight)
  (when cedille-mode-autohighlight-matching-variables (cedille-mode-highlight-occurrences)))

(make-variable-buffer-local
 (defvar cedille-mode-matching-nodes-on cedille-mode-autohighlight-matching-variables
   "Indicates if the user turned matching variable highlighting on or off for the specific node (toggled by typing 'H')"))

(make-variable-buffer-local
 (defvar cedille-mode-matching-nodes-map nil
   "Maps location tags to a list of spans of matching occurrences"))

(defun cedille-mode-interactive-highlight-loc-if (location term)
  "Returns t if LOCATION is non-nil, is not missing, and term is a variable"
  (and location (not (equal location "missing - missing")) (assoc 'symbol (se-term-data term))))

(defun cedille-mode-matching-nodes-init()
  "Initializes `cedille-mode-matching-nodes-map'"
  (let ((addf (lambda (rec-fn l k v)
                (if l
                    (if (equal k (caar l))
                        (cons (cons k (cons v (cdar l))) (cdr l))
                      (cons (car l) (funcall rec-fn rec-fn (cdr l) k v)))
                  (cons (cons k (cons v nil)) nil)))))
    (setq
     cedille-mode-matching-nodes-map
     (se-foldr
      se-mode-spans
      nil
      (lambda (span x)
        (let ((location (cdr (assoc 'location (se-span-data span)))))
          (if (cedille-mode-interactive-highlight-loc-if location span)
              (funcall addf addf x location (cons (se-span-start span) (se-span-end span)))
            x)))))))

(defun cedille-mode-highlight-occurrences()
  "Highlights matching occurrences of the selected node, if it is a variable"
  (interactive)
  (cedille-mode-clear-interactive-highlight)
  (setq cedille-mode-matching-nodes-on t)
  (when (se-mode-selected)
    (let ((location (cdr (assoc 'location (se-term-data (se-mode-selected))))))
      (when (cedille-mode-interactive-highlight-loc-if location (se-mode-selected))
        (se-foldr
         (cdr (assoc location cedille-mode-matching-nodes-map))
         nil
         (lambda (start-end x)
           (let ((overlay (make-overlay (car start-end) (cdr start-end))))
             (overlay-put overlay 'cedille-matching-occurrence t)
             (overlay-put overlay 'face `(:background ,cedille-mode-autohighlight-color)))))))))

(defun cedille-mode-clear-interactive-highlight()
  (remove-overlays nil nil 'cedille-matching-occurrence t))

(defun cedille-mode-interactive-highlight()
  "Interactive command to call cedille-mode-highlight-occurences"
  (interactive)
  (cedille-mode-clear-interactive-highlight)
  (setq cedille-mode-matching-nodes-on (not cedille-mode-matching-nodes-on))
  (when cedille-mode-matching-nodes-on (cedille-mode-highlight-occurrences)))

(defun cedille-mode-apply-tags (str tags)
  "Helper for `cedille-mode-apply-tag'"
  (if (null tags)
      str
    (let* ((tag (car tags))
           (tail (cdr tags))
           (start (cdr (assoc 'start (cdr tag))))
           (end (cdr (assoc 'end (cdr tag))))
           (data (cdr tag))
           (symbol (car tag)))
      (cedille-mode-apply-tags (se-pin-data start end symbol data str) tail))))

(defun cedille-mode-apply-tag (tag)
  "Applies the tags in TAG to its value"
  (cons
   (car tag)
   (funcall
    (if (not (string= 'binder (car tag))) 'identity 'cedille-mode-parse-binder)
    (cedille-mode-apply-tags (cadr tag) (caddr tag)))))

(defun cedille-mode-parse-binder (binder)
  "Parses the `cedille-mode-sep'-delimited binder information, returning it as an alist"
  (map
   'list
   (lambda (kv)
     (let ((i (search ":" kv)))
       (cons (intern (substring kv 0 i)) (substring kv (1+ i)))))
   (split-string binder cedille-mode-sep)))

(defun cedille-mode-prettyprint (dest)
  "Prettyprints the current file, writing to DEST"
  (interactive "FPrettyprint to: ")
  (let ((fn (buffer-file-name)))
    (if (null fn)
        (message "Buffer must have a file associated with it to prettyprint")
      (se-inf-interactive
       (cedille-mode-concat-sep "interactive" "pretty" (expand-file-name fn) (expand-file-name dest))
       (lambda (response &rest extra) (message response))
       nil))))

(defun cedille-mode-elaborate(dir)
  "Elaborates the current file"
  (interactive "GElaboration output: ")
  (let ((dir2 (expand-file-name dir)))
    (se-inf-interactive (cedille-mode-concat-sep "elaborate" (buffer-file-name) dir2)
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
  (setq cedille-mode-caching nil
        cedille-mode-print-caching-finished nil)
  (se-inf-stop)
  (se-inf-header-timer-stop)
  (cedille-mode-start-process)
  (message "Restarted cedille process")
  (cedille-mode-quit))

(defun cedille-mode-quit-and-delete()
  "Quit Cedille mode and delete forward char"
  (interactive)
  (cedille-mode-quit)
  (delete-forward-char 1))

(defun cedille-mode-quit-and-backspace()
  "Quit Cedille mode and delete backward char"
  (interactive)
  (cedille-mode-quit)
  (delete-backward-char 1))

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
  (se-navi-define-key mode (kbd "H") #'cedille-mode-interactive-highlight)
  (se-navi-define-key mode (kbd "g") #'se-mode-clear-selected)
  (se-navi-define-key mode (kbd "q") #'cedille-mode-quit)
  (se-navi-define-key mode (kbd "Q") #'cedille-mode-quit-keep-mark)
  (se-navi-define-key mode (kbd "M-s") #'cedille-mode-quit)
  (se-navi-define-key mode (kbd "C-g") #'cedille-mode-quit)

  (se-navi-define-key mode (kbd "<backspace>") #'cedille-mode-quit-and-backspace)
  (se-navi-define-key mode (kbd "<delete>")    #'cedille-mode-quit-and-delete)
  (se-navi-define-key mode (kbd "C-d")    #'cedille-mode-quit-and-delete)

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
  (se-navi-define-key mode (kbd "c") (make-cedille-mode-buffer (cedille-mode-context-buffer) lambda cedille-context-view-mode nil t))
  (se-navi-define-key mode (kbd "C") (make-cedille-mode-buffer (cedille-mode-context-buffer) lambda cedille-context-view-mode t t))
  (se-navi-define-key mode (kbd "s") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode nil nil))
  (se-navi-define-key mode (kbd "S") (make-cedille-mode-buffer (cedille-mode-summary-buffer) cedille-mode-summary cedille-summary-view-mode t nil))
  (se-navi-define-key mode (kbd "#") #'cedille-mode-highlight-occurrences)
  (se-navi-define-key mode (kbd "m") (make-cedille-mode-buffer (cedille-mode-meta-vars-buffer) lambda cedille-meta-vars-mode nil t))
  (se-navi-define-key mode (kbd "M") (make-cedille-mode-buffer (cedille-mode-meta-vars-buffer) lambda cedille-meta-vars-mode t t))
  (se-navi-define-key mode (kbd "K") #'cedille-mode-restart-backend)
  (se-navi-define-key mode (kbd "h") (make-cedille-mode-info-display-page nil))
  (se-navi-define-key mode (kbd "E") #'cedille-mode-elaborate)
  (se-navi-define-key mode (kbd "C-h 1") #'cedille-mode-highlight-default)
  (se-navi-define-key mode (kbd "C-h 2") #'cedille-mode-highlight-language-level)
  (se-navi-define-key mode (kbd "C-h 3") #'cedille-mode-highlight-checking-mode)
  (se-navi-define-key mode (kbd "$") (make-cedille-mode-customize "cedille"))
  (se-navi-define-key mode (kbd "&") #'cedille-mode-prettyprint)
  (se-navi-define-key mode (kbd "1") #'delete-other-windows)
  (se-navi-define-key mode (kbd "P") (lambda () (interactive) (message "se-mode-selected: %s" (se-mode-selected))))
  (se-navi-define-key mode (kbd "?") #'cedille-mode-backend-debug)
  (se-navi-define-key mode (kbd "x") #'cedille-mode-scratch-toggle)
  (se-navi-define-key mode (kbd "X") (lambda () (interactive) (cedille-mode-scratch-toggle t)))
  (se-navi-define-key mode (kbd "M-c") #'cedille-mode-scratch-copy-span)
  (se-navi-define-key mode (kbd "+") (make-cedille-mode-resize-current-window 1))
  (se-navi-define-key mode (kbd "-") (make-cedille-mode-resize-current-window -1))
  (se-navi-define-key mode (kbd "=") #'cedille-mode-unlock-current-window-size)
  (se-navi-define-key mode (kbd "C-x 2") #'cedille-mode-split-window)
  ; Interactive commands
  (se-navi-define-key mode (kbd "C-i h") #'cedille-mode-head-normalize)
  (se-navi-define-key mode (kbd "C-i n") #'cedille-mode-normalize)
  (se-navi-define-key mode (kbd "C-i u") #'cedille-mode-single-reduction)
  (se-navi-define-key mode (kbd "C-i e") #'cedille-mode-erase)
  (se-navi-define-key mode (kbd "C-i b") 'cedille-mode-br)
  (se-navi-define-key mode (kbd "C-i B") 'cedille-mode-br-node)
  (se-navi-define-key mode (kbd "C-i t") 'cedille-mode-br-type)
  (se-navi-define-key mode (kbd "C-i r") #'cedille-mode-inspect-clear)
  (se-navi-define-key mode (kbd "C-i R") #'cedille-mode-inspect-clear-all))

(cedille-modify-keymap 'cedille-mode)

(require 'cedille-mode-beta-reduce)

(defun cedille-mode-get-message-from-filename(filename)
  "Get the message to send to the backend, from the name of the file to parse."
  (concat "check§" filename))

(defun cedille-mode-progress-fn (response &optional oc buffer span)
  "The function called when a progress update is received from the backend"
  (setq header-line-format nil)
  (se-inf-queue-header response)
  (se-inf-next-header)
  cedille-mode-progress-msg)

(defun cedille-mode-ask-quit ()
  (or (not cedille-mode-caching)
      (progn
        (setq cedille-mode-print-caching-finished t)
        (y-or-n-p "Cedille is still caching. Do you want to kill the process? "))))

(defun cedille-mode-caching-start (&rest args)
  "Sends a stub request to the backend and waits for a response, indicating that writing .cede files has finished"
  (se-inf-interactive
   (lambda (&rest args)
     (setq cedille-mode-caching t)
     cedille-mode-status-msg)
   (lambda (&rest args)
     (when cedille-mode-print-caching-finished
       (message "Cedille caching finished"))
     (setq cedille-mode-caching nil
           cedille-mode-caching-queued nil
           cedille-mode-print-caching-finished nil))
   nil))

(defun cedille-mode-caching-hook ()
  "Hook run before an interactive request that checks if the backend is caching"
  (when (and cedille-mode-caching (not cedille-mode-caching-queued))
    (setq cedille-mode-caching-queued t)
    (se-inf-queue-header cedille-mode-caching-header)))

(defun cedille-mode-start-process ()
  "Starts the Cedille process"
  (se-inf-start (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS")))

(se-create-mode "cedille" nil
  "Major mode for Cedille files."

  (setq-local comment-start "--")

  (cedille-mode-start-process)
  ;;(or (get-buffer-process "*cedille-mode*") ;; reuse if existing process
    ;;   (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS")))
  (add-hook 'se-inf-post-parse-hook 'cedille-mode-caching-start t t)
  (add-hook 'se-inf-init-spans-hook 'cedille-mode-set-error-spans t t)
  (add-hook 'se-inf-init-spans-hook 'cedille-mode-initialize-spans t t)
  (add-hook 'se-inf-init-spans-hook 'cedille-mode-highlight-default t t)
  (add-hook 'se-inf-pre-parse-hook 'cedille-mode-clear-buffers nil t)
  (add-hook 'se-inf-pre-interactive-hook 'cedille-mode-caching-hook nil t)
  (add-hook 'deactivate-mark-hook 'cedille-mode-highlight-occurrences t)
  (add-hook 'kill-emacs-query-functions 'cedille-mode-ask-quit)

  (setq-local se-inf-get-message-from-filename 'cedille-mode-get-message-from-filename)
  (setq-local se-inf-progress-fn 'cedille-mode-progress-fn)
  (setq-local se-inf-progress-prefix cedille-mode-progress-prefix) 

  (set-input-method "Cedille"))

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
          ("\\E" "∃") ("\\F" "φ") ("\\m" "μ") ("\\c" "σ")
          ("\\\\" "\\")

          ("\\rho" "ρ") ("\\theta" "θ") ("\\epsilon" "ε") ("\\phi" "φ"); add some more of these
 ))

(defcustom cedille-mode-hook ()
  "List of functions to run after `cedille-mode' is enabled."
  :group 'cedille
  :type 'hook
  :options nil
  )

(provide 'cedille-mode)
;;; cedille-mode.el ends here
