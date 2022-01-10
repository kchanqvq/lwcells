(uiop:define-package lwcells
  (:use #:common-lisp)
  (:export #:careful-eql #:make-cell
           #:cell-p #:cell-no-news-p #:cell-ref #:update-deps
           #:make-rule #:rule-p #:rule-functions #:*rule*
           #:add-observer #:remove-observer
           #:make-computed-cell #:cell #:cell* #:defcell
           #:let-cell #:let*-cell))
(in-package :lwcells)

(defun careful-eql (old-value new-value)
  "Test observational equivalent assignment.
Currently, we use `eql' test on primitive immutable objects,
and conservatively return nil otherwise.
This scheme is safe even if the value is mutated destructively."
  (typecase old-value
    ((or symbol number) (eql old-value new-value))))

(defstruct cell
  "A primitive reactive cell.
DEPS is a list of rules that depend on this cell.
NO-NEWS-P is a function to test if OLD-VALUE and NEW-VALUE
of the cell are equivalent during assignment."
  value deps (no-news-p 'careful-eql))

(defvar *rule* nil)

(defun cell-ref (cell)
  (when *rule*
    (pushnew *rule* (cell-deps cell))
    (pushnew cell (rule-inputs *rule*)))
  (cell-value cell))

(defun update-deps (cell)
  "Force invoking dependent rules of CELL."
  (mapc #'invoke-rule (cell-deps cell)))

(defun (setf cell-ref) (new-value cell)
  (let ((old-value (cell-value cell)))
    (setf (cell-value cell) new-value)
    (when (cell-deps cell)
      (unless (funcall (cell-no-news-p cell) old-value new-value)
        (update-deps cell))))
  new-value)

(defstruct rule
  "A primitive rule.
INPUTS is the list of cells the rule depends on."
  inputs function)

(defstruct (observer-rule (:include rule)))

(defmethod invoke-rule ((rule rule))
  (dolist (input (rule-inputs rule))
    (alexandria:deletef (cell-deps input) rule))
  (setf (rule-inputs rule) nil)
  (let ((*rule* rule))
    (funcall (rule-function rule))))

(defmethod invoke-rule ((rule observer-rule))
  (let (*rule*)
    (apply (observer-rule-function rule)
           (observer-rule-inputs rule))))

(defun make-computed-cell (function &rest args)
  (let ((new-cell (apply #'make-cell args)))
    (invoke-rule
     (make-rule :function
                (lambda ()
                  (setf (cell-ref new-cell) (funcall function)))))
    new-cell))

(defun add-observer (cell function)
  (check-type function (or function symbol))
  (let ((new-rule (make-observer-rule :inputs (list cell) :function function)))
    (pushnew new-rule (cell-deps cell) :key 'observer-rule-function)))

(defun remove-observer (cell function)
  (check-type function (or function symbol))
  (alexandria:deletef (cell-deps cell) function :key 'observer-rule-function))

(defmacro cell (&body body)
  `(make-computed-cell (lambda () ,@body)))

(defmacro cell* (options &body body)
  `(make-computed-cell (lambda () ,@body) ,@options))

(defun cell-name (symbol)
  (intern (concatenate 'string (symbol-name symbol) "-CELL")))
(defmacro defcell (var val)
  `(progn
     (define-symbol-macro ,var (cell-ref ,(cell-name var)))
     (defvar ,(cell-name var) (cell ,val))))
(defmacro bind-cell (binder bindings &body body)
  (setq bindings (mapcar (lambda (binding) (if (consp binding) binding (list binding))) bindings))
  `(symbol-macrolet
       ,(mapcar (lambda (binding) `(,(car binding) (cell-ref ,(cell-name (car binding))))) bindings)
     (,binder ,(mapcar (lambda (binding) `(,(cell-name (car binding)) (cell ,(cadr binding)))) bindings)
              ,@body)))
(defmacro let-cell (bindings &body body)
  `(bind-cell let ,bindings ,@body))
(defmacro let*-cell (bindings &body body)
  `(bind-cell let* ,bindings ,@body))

(defmacro defmodel (class directsupers slotspecs &rest options)
  "Similar to `defclass', but supporting defining cell slots.

All slot definitions are by default treated as cell slots.  Pass :cell
nil to make an ordinary slot. A cell slot's :initform contains the
definition expression for its cell, and can refer to other cell slots
defined before it using (<accessor> self)."
  (let (cell-slots cell-accessors cell-initforms)
    (setq slotspecs
          (loop for slotspec in slotspecs
                collect (destructuring-bind
                            (slot &rest slotargs
                             &key (cell t) (accessor slot) (initform 'unbound)
                             &allow-other-keys)
                            slotspec
                          (if cell
                              (let ((slotargs (copy-list slotargs)))
                                (push slot cell-slots)
                                (push accessor cell-accessors)
                                (push initform cell-initforms)
                                (remf slotargs :cell)
                                (remf slotargs :accessor)
                                (remf slotargs :initform)
                                (cons slot slotargs))
                              slotspec))))
    (psetq cell-slots (nreverse cell-slots)
           cell-accessors (nreverse cell-accessors)
           cell-initforms (nreverse cell-initforms))
    `(progn
       (defclass ,class ,directsupers
         ,slotspecs ,@options)

       ,@(mapcar (lambda (slot accessor)
                   `(progn
                      (defmethod ,accessor ((object ,class))
                        (cell-ref (slot-value object ',slot)))
                      (defmethod (setf ,slot) (new-value (object ,class))
                        (setf (cell-ref (slot-value object ',slot)) new-value))))
                 cell-slots cell-accessors)

       (defmethod initialize-instance ((self ,class) &key)
         (call-next-method)
         ,@(mapcar (lambda (slot)
                     ;; some :initarg may have assign an ordinary value to a cell slot,
                     ;; wrap such value with a cell object.
                     `(when (slot-boundp self ',slot)
                        (unless (cell-p (slot-value self ',slot))
                          (setf (slot-value self ',slot)
                                (make-cell :value (slot-value self ',slot))))))
                   cell-slots)
         ,@(mapcar (lambda (slot initform)
                     ;; some cell :initform may have been overriden by an provided :initarg
                     `(unless (slot-boundp self ',slot)
                        (setf (slot-value self ',slot)
                              (cell ,initform))))
                   cell-slots cell-initforms)))))
