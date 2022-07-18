(define (composeFunc [f : (Integer -> Integer)] [g : (Integer -> Integer)]) : (Integer -> Integer)
					 (lambda: ([x : Integer]) : Integer
							  (f (g x))))


(define (addN [n : Integer]) : (Integer -> Integer)
			(lambda: ([x : Integer]) : Integer
					 (+ x n)))


((composeFunc (addN 5) (addN 7)) 11)
