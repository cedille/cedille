
(defun se--create-test-spans ()
  (mapcar
   (se-curry #'apply 'se-new-span)
   '(("L1" 1 100)
     ("L2" 1 20)
     ("L3" 1 10)
     ("L2" 21 50)
     ("L2" 50 100)
     ("L1" 101 110)
     ("L3" 30 40)
     ("L3" 41 50))))

(defun se--create-test-tree ()
  (se-create-parse-tree (se--create-test-spans)))

(ert-deftest se-term-helpers ()
  "Test that term helper methods work."
  (let* ((span1 (se-new-span "L1" 1 10))
	 (node1 (se-new-node span1 nil)))
    (should (equal (list span1) (se-as-spans (list node1))))
    (should (equal span1 (se-first-span node1)))
    (should (equal span1 (se-last-span node1)))
    (should (equal "L1" (se-term-name node1)))
    (should (equal 1 (se-term-start node1)))
    (should (equal 10 (se-term-end node1)))
    (should (equal 9 (se-term-length node1)))
    (should (se-point-in-term-p 9 node1))
    (should-not (se-point-in-term-p 0 node1))
    (should (se-term-equal-p span1 node1))
    ))

(ert-deftest se-term-end-regression1 ()
  "should not fail when children don't equal parent length"
  (let* ((tree (se--create-test-tree))
	 (span (se-find-span (se-new-span "L2" 1 20) tree)))
    (should (= 20 (se-term-end span)))))

(ert-deftest se-term-end-regression2 ()
  "should not fail when given a list"
  (should (se-term-end (se--create-test-tree))))

(ert-deftest se-last-span-regression ()
  "should not reach `max-lisp-eval-depth'"
  (should (se-last-span (se--create-test-tree)))
  )

(ert-deftest se-span-helpers ()
  "Test that se-span helpers work."
  (let ((span1 (se-new-span "L1" 1  10))
	(span2 (se-new-span "L2" 2   5))
	(span3 (se-new-span "L1" 11 20)))
    (should (se-term-before-p span1 span2))
    (should (se-term-before-p span1 span3))
    (should (se-term-before-p span2 span3))
    (should (se-term-child-p span1 span1))
    (should (se-term-child-p span2 span1))
    (should-not (se-term-child-p span2 span3))
    ))

(ert-deftest se-parse-tree ()
  "Test parse tree creation."
  (should (se--create-test-tree))
  (should (equal (sort (se--create-test-spans) #'se-term-before-p)
		 (se-flatten (se--create-test-tree)))))

(ert-deftest se-parse-tree-regression1 ()
  "Parse tree should not require pre-sorted spans."
  (should (se-create-parse-tree
	   (list (se-new-span "L1" 20 30)
		 (se-new-span "L1"  1 10)))))

(ert-deftest se-parse-tree-regression2 ()
  "Parse tree should not allow overlapping spans.  Failure \
expected, unsure if test is needed."
  (let ((bad-span (se-new-span "" 19 21)))
    (should-not (se-create-parse-tree
		 (cons bad-span (se--create-test-spans))))))

(ert-deftest se-find-methods ()
  (let* ((tree (se--create-test-tree))
	 (span1 (se-new-span "L3" 1 10))
	 (node1 (se-new-node span1 nil))
	 (span2 (se-new-span "L3" 5 30))
	 (span3 (se-new-span "L3" 30 40)))
    ;; se-find-point
    (should (= 10 (se-term-end (se-find-point 1 tree))))
    (should (se-node-p (se-find-point 1 tree)))
    ;; se-find-point-path
    (should (= 3 (length (se-find-point-path 1 tree))))
    (should (every #'se-node-p (se-find-point-path 1 tree)))
    ;; se-find-span
    (should (se-node-p (se-find-span span1 tree)))
    (should-not (se-find-span span2 tree))
    ;; se-find-span-path
    (should (= 3 (length (se-find-span-path span1 tree))))
    (should (= 3 (length (se-find-span-path node1 tree))))
    (should (every #'se-node-p (se-find-span-path span1 tree)))
    (should-not (se-find-span-path span2 tree))
    ;; se-find-after
    (should (= 5 (length (se-flatten (se-find-after span1 tree)))))
    ;; (should-not (se-find-after span2 tree))
    (should (= 3 (length (se-find-after span3 tree))))
    ))

(ert-deftest se-find-regression ()
  "should treat span interval as [start, end)"
  (let ((tree (se--create-test-tree))
	(span (se-new-span "L2" 50 100)))
    (should-not (se-point-in-term-p 100 span))
    (should (equal "L2" (se-term-name (se-find-point 50 tree))))
    (should (= 2 (length (se-find-point-path 50 tree))))
    ))

(ert-deftest se-find-point ()
  "should find parent node if children don't contain point"
  (let ((tree (se--create-test-tree)))
    (should (se-find-point 15 tree))))

(ert-deftest se-iteration ()
  "Test common iteration methods work."
  ;; se-filter
  (let ((tree (se--create-test-tree)))
    (should-not (se-filter (lambda (term) (string= "L4" (se-term-name term))) tree))
    (should (= 3 (length (se-filter (lambda (term) (string= "L3" (se-term-name term))) tree))))
    ))

(ert-deftest se-filter-order ()
  "should preserve order of results"
  (let* ((tree (se--create-test-tree))
	 (l3pred (lambda (term) (string= "L3" (se-term-name term))))
	 (result (se-filter l3pred tree)))
    (should (equal result (sort (copy-seq result) #'se-term-before-p)))))
