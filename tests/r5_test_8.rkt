(define (mul [n : Integer] [m : Integer]) : Integer
  (if (eq? m 1)
	n
	(+ n (mul n (- m 1)))))

(define (facCPS [n : Integer] [cont : (Integer -> Integer)]) : Integer
  (if (<= n 1)
	(cont 1)
	(facCPS (- n 1)
			(lambda: ([val : Integer]) : Integer
					 (cont (mul n val))))))


(facCPS 5 (lambda: ([x : Integer]) : Integer x))
