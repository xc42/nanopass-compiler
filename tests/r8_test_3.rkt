(define (counter [init : Integer]) : (Integer -> Integer)
  (lambda: ([cmd : Integer]) : Integer
		   (if (eq? cmd 0)
			 init
			 (begin 
			   (set! init (+ init cmd))
			   init))))

(let ([cnt (counter 5)])
  (begin
	(cnt 3)
	(cnt 4)
	(cnt 0)))
