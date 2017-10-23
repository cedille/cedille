

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
 (defvar cedille-mode-br-undo-stack nil
   "A list of br-frames that keeps track of previous trees and strings in the beta-reduction buffers"))

(make-variable-buffer-local
 (defvar cedille-mode-br-redo-stack nil
   "Like `cedille-mode-br-undo-stack', but for redo"))

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
 (defvar cedille-mode-br-span-range nil))

(make-variable-buffer-local
 (defvar cedille-mode-br-length nil))


;;;;;;;; Mode code ;;;;;;;;

(defvar cedille-br-keymap
  (progn
    (cedille-modify-keymap 'cedille-br-mode)
    (se-navi-define-key 'cedille-br-mode (kbd "q") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "M-s") #'cedille-mode-br-kill-buffer)
    (se-navi-define-key 'cedille-br-mode (kbd "C-g") #'cedille-mode-br-kill-buffer)
    ;(se-navi-define-key 'cedille-br-mode (kbd "y") #'cedille-mode-close-active-window)
    ;(se-navi-define-key 'cedille-br-mode (kbd "Y") #'cedille-mode-close-active-window)
    (se-navi-define-key 'cedille-br-mode (kbd "i") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "I") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "c") #'se-navi-nothing)
    (se-navi-define-key 'cedille-br-mode (kbd "C") #'se-navi-nothing)
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
    (se-navi-define-key 'cedille-br-mode (kbd "C-i ,") #'cedille-mode-br-undo)
    (se-navi-define-key 'cedille-br-mode (kbd "C-i .") #'cedille-mode-br-redo)
    (se-navi-define-key 'cedille-br-mode (kbd "P") #'cedille-mode-br-print-span)
    (se-navi-get-keymap 'cedille-br-mode)))
;(se-navi-define-key 'cedille-br-mode (kbd "") #'cedille-mode-br-) ; Template

(defun cedille-mode-br-print-span ()
  (interactive)
  (message "%s" (se-mode-selected)))

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
	(buffer (generate-new-buffer (cedille-mode-br-buffer-name)))
	(context (cedille-mode-get-context se-mode-not-selected))
	(highlight-spans cedille-mode-highlight-spans)
	(len (buffer-size)))
    (with-current-buffer buffer
      (cedille-mode-get-create-window)
      (se-navigation-mode)
      (cedille-br-mode)
      (se-inf-start (start-process "cedille-mode" "*cedille-mode*" cedille-program-name "+RTS" "-K1000000000" "-RTS"))
      (setq se-mode-not-selected se-mode-parse-tree
	    se-inf-response-finished t
	    cedille-mode-br-filename original-filename
	    cedille-mode-br-temp-str str
	    cedille-mode-br-in-buffer t
	    cedille-mode-br-length len
	    cedille-mode-global-context context
	    se-inf-filename #'cedille-mode-br-get-filename
	    se-inf-filename-base #'cedille-mode-br-get-filename-base
	    se-inf-modify-response #'cedille-mode-strip-ws
	    buffer-read-only nil
	    window-size-fixed nil)
      (se-inf-interactive (cedille-mode-get-message-from-filename cedille-mode-br-filename) nil :header "Parsing")
      (cedille-mode-br-erase str)
      (display-buffer buffer)
      (setq buffer-read-only t)
      (cedille-mode-highlight-default))
    (cedille-mode-rebalance-windows)
    buffer))

(defun cedille-mode-br-erase (s)
  "Erases the text before parsing"
  (se-inf-interactive
   (cedille-mode-erase-request-text-h s cedille-mode-br-length cedille-mode-br-filename (cedille-mode-normalize-local-context-to-string cedille-mode-global-context))
   'cedille-mode-br-erase-response
   :extra (current-buffer)
   :header "Erasing"))

(defun cedille-mode-br-erase-response (response oc buffer)
  "Receives the erased response from the backend"
  (with-current-buffer buffer
    (let ((buffer-read-only nil)
	  (response (se-markup-propertize response)))
      (if (cedille-mode-br-is-error response)
	  (progn
	    (with-selected-window (get-buffer-window) (cedille-mode-close-active-window))
	    (message "Parse error"))
	(setq cedille-mode-br-temp-str response)
	(erase-buffer)
	(insert response)
	(cedille-mode-br-parse)))))

(defun cedille-mode-br-undo ()
  "Undoes the previous buffer change"
  (interactive)
  (if (null cedille-mode-br-undo-stack)
      (message "No further undo information")
    (push (cedille-mode-br-current-frame) cedille-mode-br-redo-stack)
    (cedille-mode-br-revert (pop cedille-mode-br-undo-stack))))

(defun cedille-mode-br-redo ()
  "Redoes the previous undo"
  (interactive)
  (if (null cedille-mode-br-redo-stack)
      (message "No further redo information")
    (push (cedille-mode-br-current-frame) cedille-mode-br-undo-stack)
    (cedille-mode-br-revert (pop cedille-mode-br-redo-stack))))

(defun cedille-mode-br-parse ()
  (interactive)
  (run-hooks 'se-inf-pre-parse-hook)
  (setq se-inf-response-finished nil)
  (se-inf-interactive (concat "interactive" "§" "br" "§" cedille-mode-br-temp-str "§" cedille-mode-br-filename) #'se-inf-process-response :span (se-mode-selected) :header "Parsing" :extra (current-buffer) :delay t))

(defun cedille-mode-br-buffer-name ()
  (concat "*cedille-beta-reduce*"))

(defun cedille-mode-br-buffer ()
  "Creates or gets the beta-reduction buffer"
  (interactive)
  (if cedille-mode-br-in-buffer
      (current-buffer)
    (get-buffer-create (cedille-mode-br-buffer-name))))

(defun cedille-mode-br-is-error (str)
  "Returns t if STR is an error JSON"
  (and (<= 10 (length response)) (string= "{\"error\":\"" (substring str 0 10))))

;;;;;;;; Starting code ;;;;;;;;
(defun cedille-mode-br-start ()
  "Opens the beta-reduction buffer with the selected node"
  (interactive)
  (let ((cedille-mode-br-original-filename (buffer-file-name))
	(node (se-mode-selected)))
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

(defun cedille-mode-br-kill-buffer ()
  "Kills the current buffer"
  (interactive)
  (let ((buffer (current-buffer))
	(window (get-buffer-window)))
    (kill-buffer buffer)
    (delete-window window)))


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
	  (push (cedille-mode-br-current-frame) cedille-mode-br-undo-stack)
	  (setq cedille-mode-br-redo-stack nil)
	  (se-inf-interactive 'cedille-mode-br-request-text 'cedille-mode-br-normalize-receive-response :span span :header (if head "Head-normalizing" "Normalizing") :extra (cons head (current-buffer))))))))

(defun cedille-mode-br-normalize-receive-response (response span oc extra)
  "Receives the normalized response from the backend"
  (with-current-buffer (cdr extra)
    (let* ((head (car extra))
	   (response (se-markup-propertize response))
	   (start (se-term-start span))
	   (end (se-term-end span))
	   (before (buffer-substring-no-properties 1 start))
	   (after (buffer-substring-no-properties end (1+ (buffer-size))))
	   (str (concat before response after)))
      (setq cedille-mode-br-temp-str str)
      (cedille-mode-br-set-range start response)
      (cedille-mode-br-parse))))

(defun cedille-mode-br-set-range (start response)
  "Sets `cedille-mode-br-span-range'"
  (setq cedille-mode-br-span-range
	(if (cedille-mode-br-has-parens-string response)
	    (cons (1+ start) (+ start (length response) -1))
	  (cons start (+ start (length response))))))

(defun cedille-mode-br-current-frame ()
  "Gets the current `br-frame'"
  (br-new-frame se-mode-parse-tree (buffer-string) cedille-mode-highlight-spans))

(defun cedille-mode-br-post-parse (&optional json)
  "Called after the file was parsed, error or no."
  (if (se-inf-get-error json)
      (progn
	(when cedille-mode-br-undo-stack
	  (cedille-mode-br-revert))
	(message "Parse error"))
    (let ((buffer-read-only nil))
      (erase-buffer)
      (insert cedille-mode-br-temp-str)
      (goto-char 1)
      (deactivate-mark)
      (cedille-mode-highlight))
    (when cedille-mode-br-span-range
      (goto-char (car cedille-mode-br-span-range))
      (push-mark (cdr cedille-mode-br-span-range) t t)
      (se-mode-set-spans)
      (cedille-mode-select-parent 1))))

(defun cedille-mode-br-revert (frame)
  "Reverts the buffer to what it was at ITEM"
  (when frame
    (let ((buffer-read-only nil))
      (setq se-mode-parse-tree (br-frame-tree frame)
	    se-mode-selected nil
	    se-mode-not-selected se-mode-parse-tree
	    cedille-mode-highlight-spans (br-frame-highlight-spans frame))
      (erase-buffer)
      (insert (br-frame-str frame))
      (cedille-mode-highlight)
      (goto-char 1)
      (deactivate-mark))))

(defun cedille-mode-br-get-message-from-filename (filename)
  (concat "BRcheck" "§" filename))

(defun cedille-mode-br-request-text (span extra)
  "Gets the text to send to the backend as a request to beta-reduce a node"
  (with-current-buffer (cdr extra)
    (let ((ex (list (cdr (assoc 'language-level (se-term-data span))) (car extra)))
	  (ap (not (cedille-mode-br-has-parens span))))
    (cedille-mode-normalize-request-text span ex ap cedille-mode-br-length))))



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

(defun cedille-mode-br-has-parens-string (str)
  "Returns t if parens surround STR"
  (let ((size (length str)))
    (and (>= size 2)
	 (string= "(" (substring str 0 1))
	 (string= ")" (substring str (1- size) size))
	 (cedille-mode-br-has-parens-string-h (substring str 1 (1- size)) 0))))

(defun cedille-mode-br-has-parens-string-h (str parens)
  "Helper for `cedille-mode-br-has-parens-string'"
  (when (>= parens 0)
    (if (equal 0 (length str))
	(equal 0 parens)
      (let ((h (substring str 0 1)))
	(cedille-mode-br-has-parens-string-h
	 (substring str 1)
	 (+ parens (if (string= "(" h) 1 (if (string= ")" h) -1 0))))))))

(provide 'cedille-mode-beta-reduce)
