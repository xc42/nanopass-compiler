(define (no-use) : Void
  (let ([i 0])
	(let ([ans 
			(while (< i 10)
		   (set! i (+ i 1)))])
	  ans)))


(begin
  (no-use)
  23)
