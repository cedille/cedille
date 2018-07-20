
(defvar script-file-name "script")
(defvar testcase-file-name ".cedille/code.cede")
(defvar expected-file-name "expected")
(defvar actual-file-name "actual")

(defun read-file-contents(file)
  (let ((b (current-buffer)))
    (with-current-buffer (find-file file)
      (let ((c (buffer-string)))
        (switch-to-buffer b)
        c))))

(defun init-test(file init)
  "Initializes a test with the test directory FILE"
  (let ((inhibit-message t)) (load "~/.emacs" nil t))
  (let* ((init (= 1 (length init)))
         (script-file (concat file "/" script-file-name))
         (testcase-file (concat file "/" testcase-file-name))
         (expected-file (concat file "/" expected-file-name))
         (actual-file (concat file "/" actual-file-name))
         (init-function
          `(lambda (&rest args)
             (load ,script-file nil t)
             (let ((result (symbol-value 'output)))
               (with-current-buffer (find-file (if ,init ,expected-file ,actual-file))
                 (erase-buffer)
                 (insert result)
                 (save-buffer)
                 (unless ,init
                   (if (string= result (read-file-contents ,expected-file))
                       (message "Sucess: %s" ,file)
                     (message "Fail: %s" ,file))))))))
    (switch-to-buffer (find-file testcase-file))
    (load (concat file "/../../cedille-mode") nil t)
    (add-hook 'se-inf-init-spans-hook 'cedille-mode-initialize-spans t)
    (add-hook 'deactivate-mark-hook 'cedille-mode-highlight-occurrences)
    (se-navigation-mode 1)
    (add-hook 'se-inf-post-parse-hook init-function t)
    (se-inf-process-response (buffer-string) (current-buffer))))


(provide 'cedille-mode-tests)
