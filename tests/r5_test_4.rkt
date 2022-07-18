(define (repeat [f : (Integer -> Integer)] [n : Integer]): (Integer -> Integer)
  (if (<= n 1)
	f
	(repeat (lambda: ([x : Integer]) : Integer (f (f x))) (- n 1))))


(define (exp [n : Integer] [m : Integer]) : Integer
  (let ([addN (lambda: ([x : Integer]) : Integer (+ x n))])
	((repeat addN m) 1)))


(exp 2 4)
