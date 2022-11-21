(define (alloc128) : Integer
  (let ([v (vector 1 2 (vector 3 4) 5 (vector (vector 6 7) (vector 8 9)) 10 (vector 11 12))])
	(+ (vector-ref v 0)
	   (+ (vector-ref (vector-ref (vector-ref v 4) 1) 1)
		  (vector-ref (vector-ref v 6) 0))))
  ) 

(define (iter [f : ( -> Integer)] [n : Integer]) : Void
  (while (> n 0)
		 (begin 
		   (f)
		   (set! n (- n 1)))))


(let ([run (iter alloc128 65)])
  0)
