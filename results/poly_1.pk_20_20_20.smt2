(declare-fun p1x () Real)
(declare-fun p1y () Real)
(declare-fun p1z () Real)
(declare-fun dummy () Real)
(define-fun h () Real 20.0)
(assert (>= p1x 0))
(assert (>= p1y 0))
(assert (>= p1z 0))
(assert (<= p1x 15))
(assert (<= p1y 14))
(assert (<= p1z (- h 8)))
(check-sat)
(get-model)