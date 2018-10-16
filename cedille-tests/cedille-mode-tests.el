
(defvar script-file-name "script")
(defvar testcase-file-name "code.ced")
(defvar expected-file-name "expected")
(defvar actual-file-name "actual")

(defun cedille-test-read-file-contents(file)
  (let ((b (current-buffer)))
    (with-current-buffer (find-file file)
      (let ((c (buffer-string)))
        (switch-to-buffer b)
        c))))

(defun cedille-test-wait-for-response()
  (while (and se-inf-interactive-running
              (not (input-pending-p)))
    (sleep-for 0.01)))

(defun cedille-test-append-output(file str)
  "Appends STR to the end of FILE's contents"
  (with-current-buffer (find-file file)
    (goto-char (point-max))
    (insert str "\n")
    (save-buffer)))

(defun cedille-test-init(file init)
  "Initializes a test with the test directory FILE"
  ;(load "~/.emacs" nil t)
  (let* ((init (= 1 (length init)))
         (script-file (concat file "/" script-file-name))
         (testcase-file (concat file "/" testcase-file-name))
         (expected-file (concat file "/" expected-file-name))
         (actual-file (concat file "/" actual-file-name))
         (output-file (concat file "/../output"))
         (init-function
          `(lambda (&rest args)
             (load ,script-file nil t)
             (let ((result (symbol-value 'output)))
               (with-current-buffer (find-file (if ,init ,expected-file ,actual-file))
                 (erase-buffer)
                 (insert result)
                 (save-buffer)
                 (unless ,init
                   (cedille-test-append-output
                    ,output-file
                    (concat
                     (if (string= result (cedille-test-read-file-contents ,expected-file))
                         "Success" "Failure") ": " ,file))))))))
    (switch-to-buffer (find-file testcase-file))
    (load (concat file "/../../cedille-mode") nil t)
    (cedille-mode)
    (cedille-start-navigation)
    (cedille-test-wait-for-response)
    (funcall init-function)))

(defun cedille-test-perform-key-events-h(keys)
  (when keys
    (command-execute (kbd (car keys)))
    (cedille-test-wait-for-response)
    (cedille-test-perform-key-events-h (cdr keys))))

(defun cedille-test-perform-key-events(&rest keys)
  "Performs the interactive function for each key event in KEYS"
  (cedille-test-perform-key-events-h keys))

(provide 'cedille-mode-tests)
