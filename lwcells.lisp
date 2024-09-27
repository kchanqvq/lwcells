(uiop:define-package lwcells
  (:use #:common-lisp #:named-closure)
  (:export #:careful-eql #:make-eager-cell #:make-lazy-cell #:make-observer-cell
           #:cell-p #:lazy-cell-p #:eager-cell-p #:cell-no-news-p #:cell-ref
           #:deactivate #:cell-set-function #:with-delayed-evaluation
           #:cycle-error #:*cycle-limit* #:skip-evaluation #:increase-cycle-limit #:deactivate-cell
           #:add-observer #:remove-observer #:observer-cell-p
           #:cell #:cell* #:defcell #:defcell*
           #:let-cell #:let*-cell
           #:defmodel #:self)
  (:import-from #:damn-fast-priority-queue
                #:make-queue #:enqueue #:dequeue))
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
NO-NEWS-P is a function to test if OLD-VALUE and NEW-VALUE
of the cell are equivalent during assignment."
  ins outs function value (no-news-p 'careful-eql))
(defstruct (eager-cell (:include cell))
  (depth 1))
(defstruct (lazy-cell (:include cell))
  clean)
(defstruct (observer-cell (:include eager-cell)))

(defmethod print-object ((object cell) stream)
  (print-unreadable-object (object stream :type t :identity t)
    (format stream "~a ~a"
            (cell-value object)
            (cell-function object))))

(defvar *activations* (make-queue) "The eager cells to be run at the end of
this cycle of propagation.")

(defvar *delay-evaluation-p* nil "Bind this to T to delay cell evaluations.")

(defvar *cell* nil "The cell currently being run.
`cell-ref', when called, will add the referenced cell to its cell-ins.")

(defun invalidate (cell)
  "Mark dependent cells of CELL as not clean."
  (when (eager-cell-p cell)
    (enqueue *activations* cell (eager-cell-depth cell)))
  (when (lazy-cell-p cell)
    (if (lazy-cell-clean cell)
        (setf (lazy-cell-clean cell) nil)
        (return-from invalidate)))
  (mapc #'invalidate (cell-outs cell)))

(defvar *cycle-limit* 30)

(define-condition cycle-error (error)
  ((cell :initarg :cell))
  (:report (lambda (condition stream)
             (with-slots (cell) condition
               (let ((*print-circle* t))
                 (format stream "~a~%
is circularly invoked ~a time~:p, but the limit is ~a time~:p."
                         cell (1+ (eager-cell-depth cell)) *cycle-limit*))))))

(defun evaluate (cell)
  (when (cell-function cell)
    (tagbody start
       (let ((old-depth (if (eager-cell-p cell)
                        (eager-cell-depth cell)
                        0)))
         (when (and *cycle-limit* (>= old-depth *cycle-limit*))
           (restart-case
               (error 'cycle-error :cell cell)
             (skip-evaluation ()
               :report "Don't evaluate the cell this time."
               (return-from evaluate))
             (increase-cycle-limit (&optional (new-cycle-limit (+ *cycle-limit* 15)))
               :report "Increase *CYCLE-LIMIT* and try evaluating the cell again."
               (setq *cycle-limit* new-cycle-limit)
               (go start))
             (deactivate-cell ()
               :report "Prevent this cell from ever triggering again."
               (deactivate cell)
               (return-from evaluate))))
         (unwind-protect
              (let ((*cell* cell))
                (unless (observer-cell-p cell)
                  (deactivate cell))
                (setf (cell-value cell) (funcall (cell-function cell)))
                (when (eager-cell-p cell)
                  (setf (eager-cell-depth cell)
                        (1+ (reduce #'max (cell-ins cell)
                                    :initial-value 0
                                    :key (lambda (cell)
                                           (if (eager-cell-p cell)
                                               (eager-cell-depth cell)
                                               0))))))
                (when (lazy-cell-p cell)
                  (setf (lazy-cell-clean cell) :clean)))))))
  (unless (cell-ins cell)
    (setf (cell-function cell) nil))
  cell)

(defun deactivate (cell)
  (dolist (input (cell-ins cell))
    (alexandria:deletef (cell-outs input) cell))
  (when (eager-cell-p cell)
    (setf (eager-cell-depth cell) 1))
  (setf (cell-ins cell) nil))

(defun evaluate-activations ()
  (unless *delay-evaluation-p*
    (let ((*delay-evaluation-p* t))
      (loop
        (let ((cell (dequeue *activations*)))
          (unless cell (return))
          (evaluate cell))))))

(defun cell-ref (cell)
  (when *cell*
    (pushnew *cell* (cell-outs cell))
    (pushnew cell (cell-ins *cell*)))
  (when (and (lazy-cell-p cell)
             (not (lazy-cell-clean cell)))
    (evaluate cell))
  (cell-value cell))

(defun cell-set-function (cell new-function)
  (deactivate cell)
  (setf (cell-function cell) new-function)
  (invalidate cell)
  (evaluate-activations))

(defun cell-set-value (new-value cell)
  (let ((old-value (cell-value cell)))
    (deactivate cell)
    (setf (cell-value cell) new-value
          (cell-function cell) nil)
    (when (cell-outs cell)
      (unless (funcall (cell-no-news-p cell) old-value new-value)
        (mapc #'invalidate (cell-outs cell))
        (evaluate-activations))))
  new-value)

(define-setf-expander cell-ref (cell &environment env)
  (multiple-value-bind (dummies vals newval setter getter)
       (get-setf-expansion cell env)
     (let ((cell (gensym)) (store (gensym)))
       (values `(,cell ,@dummies)
               `(,getter ,@vals)
               `(,store)
               `(if ,cell (cell-set-value ,cell ,store)
                    (let ((,(car newval) (cell ,store)))
                      ,setter
                      ,store))
               `(cell-ref ,cell)))))

(defun call-with-delayed-evaluation (thunk)
  (if *delay-evaluation-p*
      (funcall thunk)
      (unwind-protect
           (let ((*delay-evaluation-p* t))
             (funcall thunk))
        (evaluate-activations))))

(defmacro with-delayed-evaluation (&body body)
  `(call-with-delayed-evaluation (lambda () ,@body)))

(defnclo observer (function) ()
  (let ((in-cells (cell-ins *cell*))
        (*cell* nil))
    (apply function in-cells)))

(defun cell-observer-function (cell)
  (when (typep (cell-function cell) 'observer)
    (slot-value (cell-function cell) 'function)))

(defun add-observer (cell function)
  (check-type function (or function symbol))
  (unless (find function (cell-outs cell) :key 'cell-observer-function)
    (push (make-observer-cell :ins (list cell) :function (make-observer function)
                              :depth (1+ (if (eager-cell-p cell)
                                             (eager-cell-depth cell)
                                             0)))
          (cell-outs cell))
    (cell-ref cell)
    function))

(defun remove-observer (cell function &key (key #'identity))
  (alexandria:deletef (cell-outs cell) function
                      :key (alexandria:compose key 'cell-observer-function))
  function)

(defmacro cell (&body body)
  `(make-lazy-cell :function (lambda () ,@body)))
(defmacro cell* (options &body body)
  `(make-lazy-cell :function (lambda () ,@body) ,@options))

(defun cell-name (symbol)
  (intern (concatenate 'string (symbol-name symbol) "-CELL")))
(defmacro defcell* (var (&rest options) val)
  (let ((cell-name (cell-name var)))
    `(progn
       (define-symbol-macro ,var (cell-ref ,(cell-name var)))
       (when (and (boundp ',cell-name) (typep (symbol-value ',cell-name) 'cell))
         (deactivate (symbol-value ',cell-name)))
       (defparameter ,cell-name (cell* ,options ,val)))))
(defmacro defcell (var val)
  `(defcell* ,var nil ,val))
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

(defmacro defmodel (class directsupers slotspecs &body options)
  "Similar to `defclass', but supporting defining cell slots.
A slot definition is treated as cell slots if it has a :cell slot option.
The expression after :cell is treated as the definition for its cell,
and can refer to other cell slots defined before it using (<accessor> self)."
  (let (cell-slots cell-accessors cell-defs)
    (setq slotspecs
          (loop for slotspec in slotspecs
                collect (destructuring-bind
                            (slot &rest slotargs
                             &key (cell 'unbound) (accessor slot)
                             &allow-other-keys)
                            slotspec
                          (if (eq cell 'unbound) slotspec
                              (let ((slotargs (copy-list slotargs)))
                                (push slot cell-slots)
                                (push accessor cell-accessors)
                                (push cell cell-defs)
                                (remf slotargs :cell)
                                (remf slotargs :accessor)
                                (cons slot slotargs))))))
    (psetq cell-slots (nreverse cell-slots)
           cell-accessors (nreverse cell-accessors)
           cell-defs (nreverse cell-defs))
    `(progn
       (defclass ,class ,directsupers
         ,slotspecs ,@options)

       ,@(mapcar (lambda (slot accessor)
                   `(progn
                      (defmethod ,accessor ((object ,class))
                        (cell-ref (slot-value object ',slot)))
                      (defmethod (setf ,accessor) (new-value (object ,class))
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
         ,@(mapcar (lambda (slot def)
                     ;; some cell :initform may have been overriden by an provided :initarg
                     `(unless (slot-boundp self ',slot)
                        (setf (slot-value self ',slot)
                              (cell ,def))))
                   cell-slots cell-defs)))))
