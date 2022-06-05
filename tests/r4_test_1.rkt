(define (sum [n : Integer]) : Integer
  (if (<= n 1)
	  1
	  (+ n (sum (- n 1)))))


(sum 10)
