(define (part [arr : (Vectorof Integer)] 
			  [low : Integer]
			  [high : Integer]
			  [cmp : (Integer Integer -> Boolean)]) : Integer
  (let ([pivot (vector-ref arr low)])
	(begin 
	  (while (< low high)
			 (begin 
			   (while (and (< low high)
						   (not (cmp (vector-ref arr high) pivot)))
					  (set! high (- high 1)))
			   (vector-set! arr low (vector-ref arr high))

			   (while (and (< low high) 
						   (cmp (vector-ref arr low) pivot))
					  (set! low (+ low 1)))
			   (vector-set! arr high (vector-ref arr low))))
	  (vector-set! arr low pivot)
	  low)))


(define (qsort [arr : (Vectorof Integer)]
			   [low : Integer]
			   [high : Integer]
			   [cmp : (Integer Integer -> Boolean)]) : Void
  (if (<= (- high low) 1)
	(void)
	(let ([mid (part arr low (- high 1) cmp)])
	  (begin 
	  (qsort arr low  mid cmp)
	  (qsort arr (+ mid 1) high cmp)))))


(define (checkOrder [arr : (Vectorof Integer)]
					[cmp : (Integer Integer -> Boolean)]) : Boolean
  (let ([l (vector-length arr)])
	(if (eq? l 1)
	  #t
	  (let ([i 0])
		(begin
		  (while (and (< i (- l 1))
					  (cmp (vector-ref arr i) (vector-ref arr (+ i 1))))
				 (set! i (+ i 1)))
		  (eq? i (- l 1)))))))

(let* ([len 20]
	   [x 100]
	   [less (lambda: ([a : Integer] [b : Integer]) : Boolean (<= a b))]
	   [greater (lambda: ([a : Integer] [b : Integer]) : Boolean (>= a b))]
	   [arr (make-vector len x)])
  (begin (vector-set! arr 0 233)
		 (vector-set! arr 19 -223)
		 (qsort arr 0 len less)
		 (let ([check-lt (checkOrder arr less)])
		   (begin (qsort arr 0 len greater)
				  (let ([check-gt (checkOrder arr greater)])
					(if (and check-lt check-gt)
					  233
					  1))))))
	
