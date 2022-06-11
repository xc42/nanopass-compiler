(define (sumTail [n : Integer] [acc : Integer]) : Integer
  (if (<= n 0)
	  acc
	  (sumTail (- n 1) (+ acc n))))


(sumTail 20 0) 
