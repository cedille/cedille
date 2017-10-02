
(require 'se-helpers)


(defstruct
    (se-span
     (:constructor se-new-span (name start end &optional data)))
  name start end data)

(defstruct
    (se-node
     (:constructor se-new-node (parent children)))
     parent children)

(defun se-create-spans (list)
  "Creates a list of spans from a list of lists.  Each sub list
with elements corresponding to `se-new-span' arguments."
  (cl-labels ((new-span (lst) (apply #'se-new-span lst)))
    (mapcar #'new-span list)))

(defun se-flatten (tree)
  "Flattens a tree of nodes, spans, and lists into a single list
of spans.  This keeps the order of elements but is inefficient."
  (typecase tree
    (null)
    (se-span
     (list tree))
    (se-node
     (cons (se-node-parent tree)
	   (se-flatten (se-node-children tree))))
    (sequence
     (loop for node in tree
	   collecting (se-flatten node) into nodes
	   finally (return (apply #'append nodes))))))

(defun se-as-spans (term)
  "se-* methods favor returning nodes instead of spans.  This
method will create a list of spans from TERM."
  (typecase term
    (se-span term)
    (se-node
     (se-as-spans (se-node-parent term)))
    (sequence
     (mapcar #'se-as-spans term))))

(defun se-first-span (term)
  "Returns the first span of TERM."
  (typecase term
    (se-span term)
    (se-node (se-first-span (se-node-parent term)))
    (cons (se-first-span (first term)))
    (t (signal 'wrong-type-argument '(term)))))

(defun se-last-span (term)
  "Returns the last span of TERM."
  (typecase term
    (se-span term)
    (se-node
     (if (se-node-children term)
	 (se-last-span (se-node-children term))
       (se-last-span (se-node-parent term))))
    (cons
     (se-last-span (first (last term))))
    (t (signal 'wrong-type-argument '(term)))))

(defun se-term-name (term)
  "Returns the first named span of TERM."
  (se-span-name (se-first-span term)))

(defun se-term-start (term)
  "Returns the first position of TERM."
  (se-span-start (se-first-span term)))

(defun se-term-end (term)
  "Returns the last position of TERM."
  (typecase term
    (se-span
     (se-span-end term))
    (se-node
     (se-term-end (se-node-parent term)))
    (cons
     (se-term-end (first (last term))))))

(defun se-term-data (term)
  "Returns the data of the first term."
  (let ((span (se-first-span term)))
    (when span
      (se-span-data span))))

(defun se-term-length (term)
  "Returns the length of TERM."
  (- (se-term-end term)
     (se-term-start term)))

(defun se-point-in-term-p (point term)
  "Checks if POINT is contained within the spans of TERM.
Intervals are treated as [start, end)."
  (se-between point (se-term-start term) (se-term-end term)))
  ;(se-term-end term) used to be (1- (se-term-end term))))

(defun se-term-equal-p (term1 term2)
  "Compares the start and end points of TERM1 and TERM2.  This
should be what equality generally means for terms."
  (and
   (equal (se-term-start term1) (se-term-start term2))
   (equal (se-term-end term1) (se-term-end term2))))

(defun se-term-before-p (a b)
  "Checks if span A should come before B.  A span spanning 1 to
100 would be before 1 to 20 because it encapsulates it."
  (let ((a-start (se-term-start a))
	(b-start (se-term-start b)))
  (or
   (< a-start
      b-start)
   (and
    (= a-start
       b-start)
    (> (se-term-end a)
       (se-term-end b))))))

(defun se-term-child-p (child parent)
  "Checks if CHILD should be encapsulated by PARENT.  The bounds
of CHILD should be inside the bounds of PARENT.  Returns true
when CHILD and PARENT have the same bounds."
  (and
   (>= (se-term-start child)
       (se-term-start parent))
   (<= (se-term-end child)
       (se-term-end parent))))

(defun se-create-parse-tree (lst)
  "Forms a tree from a sorted list of spans.  Returns nil if data is ill
formatted."
  ;; `copy-list' could be used; however, it isn't expected a user will
  ;; reuse a span list (or care if it becomes sorted).
  (let ((len (length lst))
	(spans (copy-list lst))
	(parents nil))
    (se--sorted-spans-to-tree)))

(defun se--sorted-spans-to-tree ()
  (cond
   ((null spans) nil)
   ((or (null parents)
	(se-term-child-p (first spans) (first parents)))
    (push (pop spans) parents)
    (cons
     (se-new-node (first parents) (se--sorted-spans-to-tree))
     (se--sorted-spans-to-tree)))
   (:else
    (pop parents)
    nil)))

(defun se-find-point (point tree)
  "Finds the deepest node in TREE that contains POINT."
  (typecase tree
    (se-node
     (when (se-point-in-term-p point (se-node-parent tree))
       (or (se-find-point point (se-node-children tree))
	   tree)))
    (sequence
     (se-map-1 (se-curry #'se-find-point point) tree))))

(defun se-find-range-path (start end tree)
  "Finds a series of nodes in TREE containing START and END.  Returns a
list containing nodes with the former elements as parents of the
latter."
  (typecase tree
    (se-node
     (let ((span (se-node-parent tree)))
       (when (and (se-point-in-term-p start span) (se-point-in-term-p end span))
	 (cons tree (se-find-range-path start end (se-node-children tree))))))
    (sequence
     (se-map-1 (se-curry #'se-find-range-path start end) tree))))

(defun se-find-point-path (point tree)
  "Finds a series of nodes in TREE containing POINT.  Returns a
list containing nodes with the former elements as parents of the
latter."
  ;(message "se-find-point-path %s %s" point tree)
  (typecase tree
    (se-node
     (when (se-point-in-term-p point (se-node-parent tree))
       (cons tree
	     (se-find-point-path point (se-node-children tree)))))
    (sequence
     (se-map-1 (se-curry #'se-find-point-path point) tree))))

(defun se-find-span (span tree)
  "Finds a node in TREE with `se-node-parent' equal to SPAN.
Returns nil if no node matches."
  (typecase tree
    (se-node
     (if (equal span (se-node-parent tree))
	 tree
       (se-map-1 (se-curry #'se-find-span span) (se-node-children tree))))
    (sequence
     (se-map-1 (se-curry #'se-find-span span) tree))))

(defun se-find-span-path (span tree)
  "Finds path to SPAN inside TREE.  Returns a list containing nodes with
the former elements as parents of the latter.  Returns nil if no
node matches."
  (typecase tree
    (se-node
     (cond
      ((se-term-equal-p span (se-node-parent tree))
       (list tree))
      ((se-term-child-p span (se-node-parent tree))
       (let ((temp (se-find-span-path span (se-node-children tree))))
	 (when temp
	   (cons tree temp))))))
    (sequence
     (se-map-1 (se-curry #'se-find-span-path span) tree))))

;; dead code
(defun se-find-after (term tree)
  "Collects all nodes in TREE after reaching TERM.  The node of
TERM isn't kept, nor its children."
  (typecase tree
    (se-node
     (if (se-term-equal-p term tree)
	 nil
       (se-find-after term (se-node-children tree))))
    (sequence
     (loop for (first second . nodes) on tree
	   when (null second) do (return (se-find-after term first))
	   when (se-term-before-p term second)
	   do (return (append (se-find-after term first)
			      (cons second nodes)))))))

(defun se-filter (predicate tree)
  "Filters spans, nodes, and trees.  PREDICATE should accept a
single term.  Returns a constructed list of nodes (or spans)
where PREDICATE returned a non-nil value.  Returned list
preserves order."
  (let (acc)
    (cl-labels
	((helper
	  (tree) (typecase tree
		   (se-span
		    (when (funcall predicate tree) (push tree acc)))
		   (se-node
		    (when (funcall predicate tree)
		      (push tree acc))
		    (helper (se-node-children tree)))
		   (cons
		    (dolist (term tree) (helper term))))))
      (helper tree)
      (nreverse acc))))

(defun se-mapc (function term)
  "Apply FUNCTION to each span in TERM for side effects only."
  (typecase term
    (se-span
     (funcall function term))
    (se-node
     (se-mapc function (se-node-parent term))
     (se-mapc function (se-node-children term)))
    (cons
     (dolist (node term)
       (se-mapc function node)))))

(defun se-span-from(start end)
  "Finds a span that ranges from start to end in tree"
  (let ((node (se-node-from start end)))
    (when node (se-node-parent node))))

(defun se-node-from(start end)
  "Finds a node that ranges from start to end in tree"
  (se-node-from-h start end (se-mode-parse-tree)))

(defun se-get-span (term)
  "Returns a span based on term"
  (when term
    (typecase term
      (se-span term)
      (se-node (se-get-span (se-node-parent term)))
      (sequence (se-first-span term)))))

(defun se-node-from-h(start end tree)
  "Helper for `se-node-from'"
  (typecase tree
    (se-node
     (let ((parent (se-node-parent tree)))
       (if (and (eq start (se-span-start parent)) (eq end (se-span-end parent)))
	   tree
         (se-map-1 (se-curry #'se-node-from-h start end) (se-node-children tree)))))
    (sequence
     (se-map-1 (se-curry #'se-node-from-h start end) tree))))

(defun se-copy-term(term)
  "Creates a deep copy of TERM"
  (typecase term
    (se-span
     (se-new-span (copy-sequence (se-span-name term)) (se-copy-term (se-span-start term)) (se-copy-term (se-span-end term)) (se-copy-term (se-span-data term))))
    (se-node
     (se-new-node (se-copy-term (se-node-parent term)) (se-copy-term (se-node-children term))))
    (string (copy-sequence term))
    (cons (cons (se-copy-term (car term)) (se-copy-term (cdr term))))
    (t (copy-tree term))))

(provide 'se)
