;; -*- Lisp -*-
;;
;; cl-kanren.lisp -- A Common Lisp implementation of uKanren/miniKanren.
;; Copyright (C) 2023  Tim Van den Langenbergh  <tmt_vdl@gmx.com>
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU Affero General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU Affero General Public License for more details.
;;
;; You should have received a copy of the GNU Affero General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.
(defpackage :cl-kanren
  (:documentation "CL-KANREN is a Common Lisp implementation of the uKanren and
miniKanren logic programming languages.

This implementation is based in part on the paper \"First-order miniKanren
Representation: Great for tooling and search\" by Rosenblat et al.")
  (:use :cl))

(in-package :cl-kanren)



(defstruct (var (:constructor var (name index))
                (:predicate varp))
  "A Kanren variable which can be unified."
  (name nil :type symbol :read-only t)
  (index 0 :type (integer 0) :read-only t))

(declaim (type var +initial-var+))
(defconstant +initial-var+
  (var nil 0)
  "The default initial variable.")

(declaim (ftype (function (var var) boolean) var-equal-p))
(defun var-equal-p (a b)
  "Compares variables A and B for equality."
  (= (var-index a)
     (var-index b)))

(declaim (type (integer 0) *global-index*))
(defvar *global-index*
  0
  "The current global index a var can have.")

(declaim (ftype (function (symbol) var) fresh-var))
(defun fresh-var (name)
  "Creates a fresh variable with the given NAME."
  (var name
       (incf *global-index*)))

(declaim (ftype (function (var var) (integer -1 1)) var-compare))
(defun var-compare (a b)
  "Compares two variables, returning an integer in the range [-1 1]."
  (let ((x (var-index a))
        (y (var-index b)))
    (declare (type (integer 0) x y))
    (cond ((< x y)
           -1)
          ((> x y)
           1)
          (t 0))))



(declaim (type sycamore:tree-map +empty-s+))
(defconstant +empty-s+
  (sycamore:make-tree-map #'var-compare)
  "The default empty substitution.")

(declaim (ftype (function (t sycamore:tree-map) t) walk))
(defun walk (v sub)
  "Looks up the value V is bound to in SUB.

Returns V as-is if it isn't bound to anything."
  (labels ((walk-loop (key)
             "Recursively look up KEY in the substitution."
             (let ((value (and (varp key)
                               (sycamore:tree-map-find sub key))))
               (if value
                   (walk-loop value)
                   key))))
    (walk-loop v)))

(declaim (ftype (function (var t sycamore:tree-map) boolean) occursp))
(defun occursp (x v sub)
  "Checks whether the binding of V in SUB resolves to X."
  (labels ((occurs-loop (object)
             "Iterates over OBJECT and its bindings."
             (typecase object
               (cons
                (or (occurs-loop (walk (car object)
                                       sub))
                    (occurs-loop (walk (cdr object)
                                       sub))))
               (sequence
                ;; NOTE: If slow, try using lparallel.
                (and (find-if #'occurs-loop
                              (map 'list
                                   (lambda (x)
                                     (walk x sub))
                                   object))
                     t))
               (var
                (var-equal-p x object))
               (otherwise
                nil))))
    (declare (ftype (function (t) boolean) occurs-loop))
    (occurs-loop v)))

(declaim (ftype (function (var t sycamore:tree-map)
                          (or null sycamore:tree-map))
                ext-s))
(defun ext-s (x v sub)
  "Binds X to V in SUB if it doesn't create an infinite loop."
  (and (not (occursp x v sub))
       (sycamore:tree-map-insert sub x v)))



(defstruct (state (:constructor make-state (sub))
                  (:predicate statep))
  "States track equality information using a substitution."
  (sub +empty-s+ :type sycamore:tree-map :read-only t))

(declaim (type state +empty-state+))
(defconstant +empty-state+
  (make-state +empty-s+)
  "The default empty state.")



(declaim (ftype (function (t t sycamore:tree-map)
                          (or null sycamore:tree-map))
                unify-in-sub))
(defun unify-in-sub (x y sub)
  "Tries to unify X and Y in SUB."
  (let ((u (walk x sub))
        (v (walk y sub)))
    (cond ((eql u v)
           sub)
          ((varp u)
           (if (and (varp v)
                    (var-equal-p u v))
               sub
               (ext-s u v sub)))
          ((varp v)
           (ext-s v u sub))
          ((and (consp u)
                (consp v))
           (let ((s2 (unify-in-sub (car u)
                                   (car v)
                                   sub)))
             (typecase s2
               (sycamore:tree-map
                (unify-in-sub (cdr u)
                              (cdr v)
                              s2))
               (otherwise nil))))
          ((and (typep u 'sequence)
                (typep v 'sequence))
           (let ((l (length u)))
             (declare (type (integer 0) l))
             (if (= (length v)
                    l)
                 (labels ((unify-loop (i res)
                            "Tries to unify all elements in U and V."
                            (if (or (= i l)
                                    (not res))
                                res
                                (unify-loop (1+ i)
                                            (unify-in-sub (elt u i)
                                                          (elt v i)
                                                          res)))))
                   (declare (ftype (function ((integer 0)
                                              (or null sycamore:tree-map))
                                             (or null sycamore:tree-map))
                                   unify-loop))
                   (unify-loop 0 sub))
                 nil)))
          (t
           (and (equalp u v)
                sub)))))

(declaim (ftype (function (t t state) (or (cons state null) null)) unify))
(defun unify (u v state)
  "Tries to unify U and V in the given STATE."
  (let ((sub (unify-in-sub u v (state-sub state))))
    (typecase sub
      (sycamore:tree-map
       (list (make-state sub)))
      (otherwise
       nil))))



(declaim (ftype (function (t sycamore:tree-map) t) walk*))
(defun walk* (tm sub)
  "Finds the binding of TM in SUB, recurring over sequences."
  (labels ((walk-loop (x)
             "Get the binding of X, recurs if it is a sequence."
             (let ((v (walk x sub)))
               (typecase v
                 (cons
                  (cons (walk-loop (car v))
                        (walk-loop (cdr v))))
                 (sequence
                  ;; NOTE: If slow, try using lparallel.
                  (map (type-of v)
                       #'walk-loop
                       v))
                 (otherwise
                  v)))))
    (walk-loop tm)))

(declaim (ftype (function ((integer 0)) symbol) reified-index))
(defun reified-index (n)
  "Turns N into a reified variable name."
  (intern
   (format nil "_.~D" n)))

(declaim (ftype (function (t state) t) reify))
(defun reify (tm state)
  "Finds the binding of TM in STATE, reifying any variables on the way."
  (let ((index -1))
    (declare (type (integer -1) index))
    (labels ((reify-loop (tm sub)
               "Walk the bindings of TM in SUB and reifies variables."
               (let ((v (walk tm sub)))
                 (typecase v
                   (cons
                    (reify-loop (cdr v)
                                (reify-loop (car v)
                                            sub)))
                   (sequence
                    (let ((l (length v)))
                      (declare (type (integer 0) l))
                      (do* ((res sub
                                 (reify-loop (elt v i)
                                             res))
                            (i 0
                               (1+ i)))
                           ((= i l)
                            res)
                        (declare (type (integer 0) i)
                                 (type sycamore:tree-map res)))))
                   (var
                    (ext-s v
                           (reified-index (incf index))
                           sub))
                   (otherwise
                    sub)))))
      (declare (ftype (function (t sycamore:tree-map) sycamore:tree-map)
                      reify-loop))
      (walk* tm
             (reify-loop tm
                         (state-sub state))))))

(declaim (ftype (function (state) t) reify-initial-var))
(defun reify-initial-var (state)
  "Reifies `+initial-var+' in the given STATE."
  (reify +initial-var+ state))



(deftype goal nil
  "A uKanren goal."
  '(or disj2 conj2 relate ==))

(defstruct (== (:constructor == (t1 t2))
               (:predicate ==p))
  ""
  (t1 nil :read-only t)
  (t2 nil :read-only t))

(declaim (type == +initial-goal+))
(defconstant +initial-goal+
  (== nil nil)
  "The basic initial goal.")

(defstruct (disj2 (:constructor disj2 (g1 g2))
                  (:predicate disj2p))
  "Disjunction (OR) of two goals."
  (g1 +initial-goal+ :type goal :read-only t)
  (g2 +initial-goal+ :type goal :read-only t))

(defstruct (conj2 (:constructor conj2 (g1 g2))
                  (:predicate conj2p))
  "Conjunction (AND) of two goals."
  (g1 +initial-goal+ :type goal :read-only t)
  (g2 +initial-goal+ :type goal :read-only t))

(defstruct (relate (:constructor relate (thunk description))
                   (:predicate relatep))
  ""
  (thunk (lambda nil +initial-goal+) :type (function nil goal) :read-only t)
  (description nil :read-only t))

(defstruct (bind (:constructor bind (s g))
                 (:predicate bindp))
  ""
  (s nil :read-only t)
  (g +initial-goal+ :type goal :read-only t))

(defstruct (mplus (:constructor mplus (mp1 mp2))
                  (:predicate mplusp))
  ""
  (mp1 nil :read-only t)
  (mp2 nil :read-only t))

(defstruct (pause (:constructor pause (state goal))
                  (:predicate pausep))
  ""
  (state +empty-state+ :type state :read-only t)
  (goal +initial-goal+ :type goal :read-only t))



(declaim (ftype (function (t) t) execute))

(declaim (ftype (function (t) boolean) maturep))
(defun maturep (s)
  ""
  (or (not s)
      (consp s)))

(defun mature (s)
  ""
  (if (maturep s)
      s
      (mature (execute s))))

(declaim (ftype (function (state (or disj2 conj2 relate ==)) t) start))
(defun start (st g)
  ""
  (etypecase g
    (disj2
     (with-slots ((g1 g1) (g2 g2))
         g
       (execute (mplus (pause st g1)
                       (pause st g2)))))
    (conj2
     (with-slots ((g1 g1) (g2 g2))
         g
       (execute (bind (pause st g1)
                      g2))))
    (relate
     (pause st
            (funcall (relate-thunk g))))
    (==
     (with-slots ((t1 t1) (t2 t2))
         g
       (unify t1 t2 st)))))

(defun execute (s)
  ""
  (typecase s
    (mplus
     (with-slots ((s1 mp1) (s2 mp2))
         s
       (let ((s3 (if (maturep s1)
                     s1
                     (execute s1))))
         (typecase s3
           (null
            s2)
           (cons
            (cons (car s3)
                  (mplus s2
                         (cdr s3))))
           (otherwise
            (mplus s2 s3))))))
    (bind
     (with-slots ((s1 s) (g g))
         s
       (declare (type goal g))
       (let ((s2 (if (maturep s1)
                     s1
                     (execute s1))))
         (typecase s2
           (null nil)
           (cons
            (execute (mplus (pause (car s2)
                                   g)
                            (bind (cdr s2)
                                  g))))
           (otherwise
            (bind s2 g))))))
    (pause
     (with-slots ((st state) (g goal))
         s
       (declare (type state st)
                (type goal g))
       (start st g)))
    (otherwise s)))



(declaim (ftype (function (state goal) (or null pause)) prune-goal))
(defun prune-goal (st g)
  ""
  (flet ((prune-term (term)
           ""
           (walk* term
                  (state-sub st))))
    (etypecase g
      (disj2
       (with-slots ((g1 g1) (g2 g2))
           g
         (declare (type goal g1 g2))
         (let ((pg (prune-goal st g1)))
           (etypecase pg
             ;; If the first goal fails we try the second goal.
             (null (prune-goal st g2))
             ;; Otherwise...
             (pause
              (with-slots ((st1 state) (g3 goal))
                  pg
                (declare (type state st1)
                         (type goal g3))
                (let ((pg2 (prune-goal st g2)))
                  (etypecase pg2
                    ;; If the second goal fails we pause the continuation of
                    ;; the first goal.
                    (null (pause st1 g3))
                    ;; Otherwise we pause the disjunction of the continuations
                    ;; of the first and second goals.
                    (pause
                     (pause st
                            (disj2 g3
                                   (pause-goal pg2))))))))))))
      (conj2
       (with-slots ((g1 g1) (g2 g2))
           g
         (declare (type goal g1 g2))
         (let ((pg (prune-goal st g1)))
           (etypecase pg
             ;; If the first goal fails, we fail.
             (null nil)
             (pause
              (with-slots ((st1 state) (g3 goal))
                  pg
                (declare (type state st1)
                         (type goal g3))
                (let ((pg2 (prune-goal st1 g2)))
                  (etypecase pg2
                    ;; If the second goal fails, we fail.
                    (null nil)
                    ;; Otherwise we pause the conjunction of the continuations
                    ;; of the first and second goals.
                    ;; IOW we pause (AND (cont g1) (cont g2)).
                    (pause
                     (pause (pause-state pg2)
                            (conj2 g3
                                   (pause-goal pg2))))))))))))
      (relate
       (with-slots ((thunk thunk) (d description))
           g
         (declare (type (function nil goal) thunk))
         (pause st
                (relate thunk
                        (prune-term d)))))
      (==
       (with-slots ((t1 t1) (t2 t2))
           g
         (let ((t3 (prune-term t1))
               (t4 (prune-term t2)))
           (let ((st2 (unify t3 t4 st)))
             (etypecase st2
               (null nil)
               ((cons state null)
                (pause (car st2)
                       (== t3 t4)))))))))))

(defun prune-stream (s)
  ""
  (typecase s
    (mplus
     (with-slots ((s1 s1) (s2 s2))
         s
       (let ((ps (prune-stream s1)))
         (if (not ps)
             (prune-stream s2)
             (let ((ps2 (prune-stream s2)))
               (if (not ps2)
                   ps
                   (mplus ps ps2)))))))
    (bind
     (with-slots ((s s) (g g))
         s
       (declare (type goal g))
       (let ((ps (prune-stream s)))
         (typecase ps
           (null nil)
           ((cons state null)
            (prune-goal (car ps)
                        g))
           (pause
            (with-slots ((st state) (g1 goal))
                ps
              (declare (type state st)
                       (type goal g1))
              (let ((pg (prune-goal st g)))
                (etypecase pg
                  (null nil)
                  (pause
                   (with-slots ((st1 state) (g2 goal))
                       pg
                     (declare (type state st1)
                              (type goal g2))
                     (pause st1
                            (conj2 g1 g2))))))))
           (otherwise
            (let ((pg (prune-goal +empty-state+ g)))
              (etypecase pg
                (null nil)
                (pause
                 (bind ps g)))))))))
    (pause
     (with-slots ((st state) (g goal))
         s
       (declare (type state st)
                (type goal g))
       (prune-goal st g)))
    (cons
     (cons (car s)
           (prune-stream (cdr s))))
    (otherwise
     s)))



(declaim (ftype (function (goal) goal) dnf-goal))
(defun dnf-goal (g)
  "Transform a goal G into Disjunctive Normal Form."
  (typecase g
    (conj2
     (labels ((loop2 (g1 g2)
                (typecase g2
                  (disj2
                   (disj2 (loop2 g1
                                 (disj2-g1 g2))
                          (loop2 g1
                                 (disj2-g2 g2))))
                  (otherwise
                   (conj2 g1 g2))))
              (loop1 (g1 g2)
                (typecase g1
                  (disj2
                   (disj2 (loop1 (disj2-g1 g1)
                                 g2)
                          (loop1 (disj2-g2 g1)
                                 g2)))
                  (otherwise
                   (loop2 g1 g2)))))
       (declare (ftype (function (goal goal) goal) loop1 loop2))
       (loop1 (dnf-goal (conj2-g1 g))
              (dnf-goal (conj2-g2 g)))))
    (disj2
     (with-slots ((g1 g1) (g2 g2))
         g
       (declare (type goal g1 g2))
       (disj2 (dnf-goal g1)
              (dnf-goal g2))))
    (otherwise g)))

(defun dnf-stream (s)
  "Lift disjunctions out of conjunctions.

(conj (disj A B) C) -> (disj (conj A C) (conj A B))
(conj C (disj A B)) -> (disj (conj C A) (conj C B))
(pause st (disj A B)) -> (mplus (pause st A) (pause st B))
(bind (mplus A B) C) -> (mplus (bind A C) (bind B C))
(bind C (disj A B)) -> (mplus (bind C A) (bind C B))"
  (labels ((push-pause (st g)
             (typecase g
               (disj2
                (with-slots ((g1 g1) (g2 g2))
                    g
                  (declare (type goal g1 g2))
                  (mplus (push-pause st g1)
                         (push-pause st g2))))
               (otherwise
                (pause st g)))))
    (declare (ftype (function (state goal) (or mplus pause))))
    (typecase s
      (bind
       (labels ((loop2 (s g)
                  (typecase g
                    (disj2
                     (with-slots ((g1 g1) (g2 g2))
                         g
                       (declare (type goal g1 g2))
                       (mplus (loop2 s g1)
                              (loop2 s g2))))
                    (otherwise
                     (bind s g))))
                (loop1 (s g)
                  (typecase s
                    (mplus
                     (with-slots ((sa mp1) (sb mp2))
                         s
                       (mplus (loop1 sa g)
                              (loop1 sb g))))
                    (cons
                     (mplus (push-pause (car s)
                                        g)
                            (loop1 (cdr s)
                                   g)))
                    (otherwise
                     (loop2 s g)))))
         (declare (ftype (function (t goal) (or mplus bind)) loop1 loop2))
         (with-slots ((s1 s) (g g))
             s
           (declare (type goal g))
           (loop1 (dnf-stream s1)
                  (dnf-goal g)))))
      (pause
       (push-pause (pause-state s)
                   (dnf-goal (pause-goal s))))
      (mplus
       (mplus (dnf-stream (mplus-mp1 s))
              (dnf-stream (mplus-mp2 s))))
      (cons
       (cons (car s)
             (dnf-stream (cdr s))))
      (otherwise s))))



(declaim (type goal +succeed+ +fail+))
(defconstant +succeed+
  (== t t)
  "Goal that always succeeds.")

(defconstant +fail+
  (== t nil)
  "Goal that always fails.")

(defmacro conj (&body goals)
  "Goal which succeeds if all goals succeed."
  (if (null goals)
      '+succeed+
      (reduce (lambda (a b)
                (list 'conj2 a b))
              goals
              :from-end t)))

(defmacro disj (&body goals)
  "Goal which fails if all goals fail."
  (if (null goals)
      '+fail+
      (reduce (lambda (a b)
                (list 'disj2 a b))
              goals
              :from-end t)))

(defmacro fresh (variables goal &rest goals)
  "Runs the given GOALS with the given fresh variables."
  `(let ,(mapcar (lambda (v)
                   `(,v (fresh-var ',v)))
          variables)
     (conj ,@(cons goal goals))))

(defmacro defrel (name params &body body)
  "Defines a new relation."
  (multiple-value-bind (docstring goals)
      (if (stringp (car body))
          (values (list (car body))
                  (cdr body))
          (values nil body))
    (let ((rel-body (append docstring
                            `((relate (lambda nil
                                        (fresh nil
                                               ,@goals))
                                      (list #',name
                                            'name
                                            ,@params))))))
      `(defun ,name ,params
         ,@rel-body))))

(defmacro conde (clause &rest clauses)
  "Disjoins the clauses."
  `(disj ,@(mapcar (lambda (clause)
                     (cons 'conj clause))
                   (cons clause clauses))))

(defmacro query (variables goal &rest goals)
  "Pause at a fresh query."
  (let ((g (gensym)))
    `(let ((,g (fresh ,variables
                      (== (list ,@variables)
                          +initial-var+)
                      ,@(cons goal goals))))
       (pause +empty-state+ ,g))))

(declaim (ftype (function ((or null (integer 0)) t) list) kstream-take))
(defun kstream-take (n s)
  "Take up to N results from the Kanren stream S."
  (labels ((numbered-take (n s res)
             (if (= n 0)
                 (reverse res)
                 (let ((s (mature s)))
                   (if (consp s)
                       (numbered-take (1- n)
                                      (cdr s)
                                      (cons (car s)
                                            res))
                       (reverse res)))))
           (full-take (s res)
             (let ((s (mature s)))
               (if (consp s)
                   (full-take (cdr s)
                              (cons (car s)
                                    res))
                   (reverse res)))))
    (etypecase n
      (null (full-take s nil))
      ((integer 0)
       (numbered-take n s nil)))))

(defmacro run (n &body body)
  "Run BODY until we get at most N (if any) results."
  `(mapcar #'reify-initial-var
           (kstream-take ,n
                         (query ,@body))))

(defmacro run* (&body body)
  "Run BODY until all results have been reached."
  `(run nil ,@body))



(defun explore-stream (qvars s)
  "NOT YET IMPLEMENTED."
  (declare (ignore qvars s))
  ;; (define margin "|_")
  ;; (define (pp prefix v) (pprint/margin margin prefix v))
  ;; (define (pp/qvars vs)
  ;;   (define (qv-prefix qv) (string-append "_" (symbol->string qv) "_=_"))
  ;;   (define qv-prefixes (and qvars (mapcar #'qv-prefix qvars)))
  ;;   (if qv-prefixes
  ;;     (for-each (lambda (prefix v) (pp prefix v)) qv-prefixes vs)
  ;;     (for-each (lambda (v) (pp "_" v)) vs)))
  ;; (define (print-choice s)
  ;;   (match s
  ;;     ((pause st g)
  ;;      (pp/qvars (walked-term initial-var st))
  ;;      (define cxs (walked-term (goal->constraints st g) st))
  ;;      (unless (null? cxs)
  ;;        (displayln (string-append margin "_Constraints:"))
  ;;        (for-each (lambda (v) (pp "_*_" v)) cxs))
  ;;      (when (null? cxs)
  ;;        (displayln (string-append margin "_No_constraints"))))))
  ;; (let loop ((s (stream->choices s)) (undo '()))
  ;;   (define previous-choice
  ;;     (and (pair? undo)
  ;;          (let* ((i.s (car undo)) (i (car i.s)) (s (cdr i.s)))
  ;;            (list-ref (dropf s state?) (- i 1)))))
  ;;   (define results (takef s state?))
  ;;   (define choices (dropf s state?))
  ;;   (display "\n========================================")
  ;;   (displayln "========================================")
  ;;   (unless (= (length results) 0)
  ;;     (printf "Number_of_results:_~a\n" (length results))
  ;;     (for-each (lambda (st)
  ;;                 (pp/qvars (walked-term initial-var st))
  ;;                 (newline))
  ;;               results))
  ;;   (when (and previous-choice (null? results))
  ;;     (printf "Previous choice:\n")
  ;;     (print-choice previous-choice)
  ;;     (newline))
  ;;   (printf "Current depth: ~a\n" (length undo))
  ;;   (if (= 0 (length choices))
  ;;     (if (= (length results) 0)
  ;;       (printf "Choice FAILED!  Undo to continue.\n")
  ;;       (printf "No more choices available.  Undo to continue.\n"))
  ;;     (printf "Number of choices: ~a\n" (length choices)))
  ;;   (for-each (lambda (i s)
  ;;               (printf (string-append "\n" margin "Choice ~s:\n") (+ i 1))
  ;;               (print-choice s))
  ;;             (range (length choices)) choices)
  ;;   (printf "\n[h]elp, [u]ndo, or choice number> ")
  ;;   (define (invalid)
  ;;     (displayln
  ;;       "\nInvalid command or choice number.\nHit enter to continue.")
  ;;     (read-line) (read-line)
  ;;     (loop s undo))
  ;;   (define i (read))
  ;;   (cond ((eof-object? i) (newline))
  ;;         ((or (eq? i 'h) (eq? i 'help))
  ;;          (display-line
  ;;            (string-append "\nType either the letter 'u' or the"
  ;;                           " number following one of the listed choices."
  ;;                           "\nHit enter to continue."))
  ;;          (read-line) (read-line)
  ;;          (loop s undo))
  ;;         ((and (or (eq? i 'u) (eq? i 'undo)) (pair? undo))
  ;;          (loop (cdar undo) (cdr undo)))
  ;;         ((and (integer? i) (<= 1 i) (<= i (length choices)))
  ;;          (loop (stream->choices (step (list-ref choices (- i 1))))
  ;;                (cons (cons i s) undo)))
  ;;         (else (invalid))))
  )
