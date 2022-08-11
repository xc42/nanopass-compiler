(define (nouse) : Void
  (let ([i 0])
	(let ([ans 
			(while (< i 10)
		   (set! i (+ i 1)))])
	  ans)))


(begin
  (nouse)
  23)
