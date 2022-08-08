(define (fib [n : Integer]) : Integer
  (let ([a 1])
	(let ([b 1])
	  (begin 
		(while (> n 1)
			   (let ([c (+ a b)])
				 (begin
				   (set! a b)
				   (set! b c)
				   (set! n (- n 1)))))
		a))))


(fib 10)
