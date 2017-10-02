

(require 'se)
(require 'se-mode)
(require 'se-navi)
(require 'se-inf)
(require 'se-markup)


;;;;;;;; Structures ;;;;;;;;

(defstruct
    (br-frame
     (:constructor br-new-frame (tree str highlight-spans)))
  tree str highlight-spans)



;;;;;;;; Variables ;;;;;;;;

(make-variable-buffer-local
 (defvar cedille-mode-br-history nil
   "A list of br-frames that keeps track of previous trees and strings in the beta-reduction buffers"))

(make-variable-buffer-local
 (defvar cedille-mode-br-filename nil
   "The file that contains `cedille-mode-br-str'"))

(make-variable-buffer-local
 (defvar cedille-mode-br-in-buffer nil
   "Whether or not you are in the beta-reduction buffer"))

(make-variable-buffer-local
 (defvar cedille-mode-br-temp-str nil
   "A temporary variable to hold the buffer's string (after normalization) until it is sucessfully parsed. Gets discarded upon failure."))

(make-variable-buffer-local
 (defvar cedille-mode-br-length nil))


;;;;;;;; Mode code ;;;;;;;;

(defvar cedille-br-keymap
  (progn
    (cedille-modify-keymap 'cedille-br-mode)
    (se-navi-define-key 'cedille-br-mode (kbd "q") #'cedille-mode-close-active-window)
    (se-navi-define-key 'cedille-br-mode (kbd "M-s") #'cedille-mode-close-active-window);cedille-mode-br-parse)
    (se-navi-define-key 'cedille-br-mode (kbd "C-g") #'cedille-mode-close-active-window)
    (se-navi-define-key 'cedille-br-mode (kbd "y") #'cedille-mode-close-active-window)
    (se-navi-define-key 'cedille-br-mode (kbd "Y") #'cedille-mode-close-active-window)
    (se-navi-define-key 'cedille-br-mode (kbd "i") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "I") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "r") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "R") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "t") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "t") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "s") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "S") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i e") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i b") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i n") #'cedille-mode-br-normalize)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i h") (lambda () (interactive) (cedille-mode-br-normalize t)))
    (se-navi-define-key 'cedille-br-mode (kbd "C-i r") #'cedille-mode-br-undo)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i R") #'cedille-mode-br-undo-all)
    (se-navi-define-key 'cedille-br-mode (kbd "P") #'cedille-mode-br-print-span)
    (se-navi-get-keymap 'cedille-br-mode)))

(defun cedille-mode-br-get-filename ()
  cedille-mode-br-filename)

(defun cedille-mode-br-get-filename-base (&optional filename)
  (file-name-base cedille-mode-br-filename))

(define-minor-mode cedille-br-mode
  "Minor mode for the beta-reduction buffer"
  nil " Beta-reduce" cedille-br-keymap
  (when cedille-br-mode
    (set-input-method "Cedille")
    (setq-local comment-start "%")
    (setq-local se-inf-get-message-from-filename 'cedille-mode-br-get-message-from-filename)
    (setq se-navi-current-keymap (se-navi-get-keymap 'cedille-br-mode))
    (make-local-variable 'minor-mode-overriding-map-alist)
    (push (cons 'se-navigation-mode se-navi-current-keymap)
	  minor-mode-overriding-map-alist)
    (add-hook    'se-inf-init-spans-hook  #'cedille-mode-initialize-spans  t   t)
    (add-hook    'se-inf-init-spans-hook  #'se-markup-propertize-spans     t   t)
    (add-hook    'se-inf-pre-parse-hook   #'cedille-mode-clear-buffers     nil t)
    (add-hook    'se-inf-pre-parse-hook   #'se-mode-clear-selected         t   t)
    (add-hook    'se-inf-post-parse-hook  #'cedille-mode-br-post-parse     t   t)
    (remove-hook 'se-inf-pre-parse-hook   #'save-buffer                        t)
    (remove-hook 'before-change-functions #'se-navigation-mode-quit            t))
  (unless cedille-br-mode
    (message "quitting cedille-br-mode")))


;;;;;;;; Buffer/file code ;;;;;;;;

(defun cedille-mode-br-init-buffer (str)
  "Initializes the beta-reduction buffer"
  (let ((original-filename (buffer-file-name))
	(buffer (cedille-mode-br-buffer))
	(context (cedille-mode-get-context se-mode-not-selected))
	(highlight-spans cedille-mode-highlight-spans)
	(len (buffer-size)))
	;(process se-inf-process))
	;(whole-str (buffer-string)))
    (with-current-buffer buffer
      (cedille-mode-get-create-window)
      (se-navigation-mode)
      (cedille-br-mode)
      ;(se-inf-start process)
      (se-inf-start (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS"))
      (setq se-mode-not-selected se-mode-parse-tree
	    se-inf-response-finished t
	    cedille-mode-br-filename original-filename
	    cedille-mode-br-temp-str str
	    cedille-mode-br-in-buffer t
	    cedille-mode-br-length len
	    se-inf-filename #'cedille-mode-br-get-filename
	    se-inf-filename-base #'cedille-mode-br-get-filename-base
	    se-inf-modify-response #'cedille-mode-strip-ws
	    buffer-read-only nil
	    window-size-fixed nil)
      (se-inf-interactive (cedille-mode-get-message-from-filename cedille-mode-br-filename) nil :header "Parsing")
      (cedille-mode-br-parse)
      (erase-buffer)
      (insert str)
      (display-buffer buffer)
      (setq buffer-read-only t)
      (cedille-mode-highlight-default))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-br-undo ()
  "Undoes the previous buffer change"
  (interactive)
  (setq cedille-mode-br-history (or (cdr cedille-mode-br-history) cedille-mode-br-history))
  (cedille-mode-br-revert))

(defun cedille-mode-br-undo-all ()
  "Resets the buffer to its original state"
  (interactive)
  (setq cedille-mode-br-history (last cedille-mode-br-history))
  (cedille-mode-br-revert))

(defun cedille-mode-br-parse ()
  (interactive)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (se-inf-interactive (concat "brParse" "§" cedille-mode-br-filename "§" cedille-mode-br-temp-str) #'se-inf-process-response :span (se-mode-selected) :header "Parsing" :extra (current-buffer) :delay t))

(defun cedille-mode-br-buffer-name ()
  (concat "*cedille-beta-reduce-" (se-inf-filename-base) "*"))

(defun cedille-mode-br-buffer ()
  "Creates or gets the beta-reduction buffer"
  (interactive)
  (if cedille-mode-br-in-buffer
      (current-buffer)
    (get-buffer-create (cedille-mode-br-buffer-name))))

(defun cedille-mode-br-is-error (str)
  "Returns t if STR is an error JSON"
  (string= "{\"error\":\"" (substring str 0 10)))

(defun cedille-mode-br-toggle (&optional jump-to-window-p)
  (interactive)
  (let* ((name (cedille-mode-br-buffer-name))
	 (buffer (get-buffer name))
	 (wndw t))
    (if (null buffer)
	(setq buffer (call-interactively #'cedille-mode-br-start))
      (setq wndw (cedille-mode-toggle-buffer-display buffer)))
    (when (and wndw jump-to-window-p)
      (select-window (get-buffer-window buffer))
      (goto-char 1)
      (deactivate-mark))
    (enlarge-window 0)
    (cedille-mode-rebalance-windows)
    buffer))

;;;;;;;; Starting code ;;;;;;;;
(defun cedille-mode-br-start ()
  "Opens the beta-reduction buffer with the selected node"
  (interactive)
  (let* ((cedille-mode-br-original-filename (buffer-file-name))
	 (node (se-mode-selected))
	 (buffer (cedille-mode-br-buffer-name))
	 (window (get-buffer-window buffer)))
    (when window (delete-window window))
    (when (get-buffer buffer) (kill-buffer buffer))
    (if node
	(cedille-mode-br-start-node (se-copy-term node))
      (call-interactively #'cedille-mode-br-start-prompt)))
  nil)

(defun cedille-mode-br-start-node (node)
  "Starts beta-reduction buffer with node"
  (let* ((start (se-term-start node))
	 (end (min (1+ (buffer-size)) (se-term-end node)))
	 (text (buffer-substring start end)))
    (cedille-mode-br-init-buffer text)))

(defun cedille-mode-br-start-prompt (input)
  "Starts beta-reduction buffer with the prompted input INPUT"
  (interactive "MBeta-reduce: ")
  (cedille-mode-br-init-buffer input))



;;;;;;;; Normalizing code ;;;;;;;;

(defun cedille-mode-br-normalize (&optional head)
  "Replace the selected span with its normalized value"
  (interactive)
  (let ((span (se-get-span (se-mode-selected))))
    (if (null span)
	(message "Error: must select a node")
      (let ((ll (cdr (assoc 'language-level (se-span-data span)))))
	(if (not (and ll (or (string= ll "term") (string= ll "type"))))
	    (message "Node must be a term or a type")
	  (se-inf-interactive 'cedille-mode-br-request-text 'cedille-mode-br-normalize-receive-response :span span :header (if head "Head-normalizing" "Normalizing") :extra (cons head (current-buffer))))))))

(defun cedille-mode-br-normalize-receive-response (response span oc extra)
  "Receives the normalized response from the backend"
  (with-current-buffer (cedille-mode-br-buffer)
    (let* ((head (car extra))
	   (response (se-markup-propertize response))
	   (str (concat (buffer-substring-no-properties 1 (se-term-start span)) response (buffer-substring-no-properties (se-term-end span) (1+ (buffer-size))))))
      (setq cedille-mode-br-temp-str str)
      (cedille-mode-br-parse))))

(defun cedille-mode-br-post-parse (&optional json)
  "Called after the file was parsed, error or no."
  (with-current-buffer (cedille-mode-br-buffer)
    (if (se-inf-get-error json)
        (progn
	  (when cedille-mode-br-history
	    (cedille-mode-br-revert))
	  (message "Parse error"))
      (let ((buffer-read-only nil))
	(erase-buffer)
	(insert cedille-mode-br-temp-str)
	(goto-char 1)
	(deactivate-mark)
	(cedille-mode-highlight))
      (push (br-new-frame se-mode-parse-tree (buffer-string) cedille-mode-highlight-spans) cedille-mode-br-history))))

(defun cedille-mode-br-revert ()
  "Reverts the buffer to what it was at ITEM"
  (with-current-buffer (cedille-mode-br-buffer)
    (when cedille-mode-br-history
      (let ((buffer-read-only nil)
	    (item (car cedille-mode-br-history)))
	(setq se-mode-parse-tree (br-frame-tree item)
	      se-mode-selected nil
	      se-mode-not-selected se-mode-parse-tree
	      cedille-mode-highlight-spans (br-frame-highlight-spans item))
	(erase-buffer)
	(insert (br-frame-str item))
	(cedille-mode-highlight)
	(goto-char 1)
	(deactivate-mark)))))

(defun cedille-mode-br-get-message-from-filename (filename)
  (concat "BRcheck" "§" filename))

(defun cedille-mode-br-request-text (span extra)
  "Gets the text to send to the backend as a request to beta-reduce a node"
  (with-current-buffer (cdr extra)
    (let ((ex (list (cdr (assoc 'language-level (se-term-data span))) (car extra)))
	  (ap (not (cedille-mode-br-has-parens span))))
    (cedille-mode-normalize-request-text span ex ap cedille-mode-br-length))))

(defun cedille-mode-br-clear-jumps ()
  "Clears all jumps"
  ; TO DO: Implement this
  )



;;;;;;;; Helper functions ;;;;;;;;

(defun cedille-mode-br-has-parens (span)
  "Returns t if parens should surround the response from normalizing SPAN"
  (let ((s (se-term-start span))
	(e (se-term-end span))
	(size (buffer-size)))
    (or (and (equal 1 s) (equal (1+ size) e))
	(when (and (< 1 s) (>= size e))
	  (let ((f (buffer-substring (1- s) s))
		(l (buffer-substring-no-properties e (1+ e))))
	    (and (string= "(" f) (string= ")" l)))))))

(provide 'cedille-mode-beta-reduce)
