(define (add [x : Integer] [y : Integer]) : Integer
  (+ x y))

(define (sub [x : Integer] [y : Integer]) : Integer
  (- x y))


((if (> (read) 0) add sub) (read) (read))
