
(eval-when-compile (require 'cl))

(defmacro se-curry (fn &rest args)
  "Returns curried function. FN should be a function symbol or a lambda. Doesn't work with local variables."
  `(lambda (&rest more-args)
     (apply ,fn ,@args more-args)))

(defun se-between (x a b)
  "Checks for X in interval [A, B]."
  (and
   (>= x a)
   (<= x b)))

(defun se-map-1 (fn list)
  "Maps elements of LIST onto FN, return first non-nil
transformed element."
  (loop while list
	thereis (funcall fn (pop list))))

(provide 'se-helpers)
