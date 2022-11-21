(let* ([n 100]
	   [arr (make-vector n 5)])
  (while (> n 0)

		 (let ([arr2 (make-vector 1024 7)])
		   (vector-set! arr (- n 1) (vector-ref arr2 2)))

		 (set! n (- n 1)))
  (vector-ref arr 4))
