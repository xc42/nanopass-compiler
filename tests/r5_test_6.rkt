(define (checkEq [v1 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
				 [v2 : (Vector Integer Integer Integer Integer Integer Integer Integer)]) : Boolean
  (if (and (eq? (vector-ref v1 0) (vector-ref v2 0))
		   (and (eq? (vector-ref v1 1) (vector-ref v2 1))
				(and (eq? (vector-ref v1 2) (vector-ref v2 2))
					 (and (eq? (vector-ref v1 3) (vector-ref v2 3))
						  (and (eq? (vector-ref v1 4) (vector-ref v2 4))
							   (and (eq? (vector-ref v1 5) (vector-ref v2 5))
									(eq? (vector-ref v1 6) (vector-ref v2 6))))))))
	#t
	#f))


(define (shiftLeft [v : (Vector Integer Integer Integer Integer Integer Integer Integer)])
  : (Vector Integer Integer Integer Integer Integer Integer Integer)
  (let ([v0 (vector-ref v 0)])
	(let ([_ (vector-set! v 0 (vector-ref v 1))])
	  (let ([_ (vector-set! v 1 (vector-ref v 2))])
		(let ([_ (vector-set! v 2 (vector-ref v 3))])
		  (let ([_ (vector-set! v 3 (vector-ref v 4))])
			(let ([_ (vector-set! v 4 (vector-ref v 5))])
			  (let ([_ (vector-set! v 5 (vector-ref v 6))])
				(let ([_ (vector-set! v 6 v0)])
				  v)))))))))



(define (shiftRight [v : (Vector Integer Integer Integer Integer Integer Integer Integer)])
  : (Vector Integer Integer Integer Integer Integer Integer Integer)
  (let ([v6 (vector-ref v 6)])
	(let ([_ (vector-set! v 6 (vector-ref v 5))])
	  (let ([_ (vector-set! v 5 (vector-ref v 4))])
		(let ([_ (vector-set! v 4 (vector-ref v 3))])
		  (let ([_ (vector-set! v 3 (vector-ref v 2))])
			(let ([_ (vector-set! v 2 (vector-ref v 1))])
			  (let ([_ (vector-set! v 1 (vector-ref v 0))])
				(let ([_ (vector-set! v 0 v6)])
				  v)))))))))

(define (repeat [sft : ((Vector Integer Integer Integer Integer Integer Integer Integer) -> (Vector Integer Integer Integer Integer Integer Integer Integer))]
				[n : Integer]) : ((Vector Integer Integer Integer Integer Integer Integer Integer) -> (Vector Integer Integer Integer Integer Integer Integer Integer))
  (if (<= n 1)
	sft
	(lambda: ([v : (Vector Integer Integer Integer Integer Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer Integer)
	  (sft ((repeat sft (- n 1)) v)))))

(define (compose [f : ((Vector Integer Integer Integer Integer Integer Integer Integer) -> (Vector Integer Integer Integer Integer Integer Integer Integer))]
				 [g : ((Vector Integer Integer Integer Integer Integer Integer Integer) -> (Vector Integer Integer Integer Integer Integer Integer Integer))])
   : ((Vector Integer Integer Integer Integer Integer Integer Integer) -> (Vector Integer Integer Integer Integer Integer Integer Integer))
  (lambda: ([v : (Vector Integer Integer Integer Integer Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer Integer)
	(f (g v))))

(let ([v1 (vector 11 22 33 44 55 66 77)])
  (let ([v2 (vector 33 44 55 66 77 11 22)])
  (let ([shiftLeft3 (repeat shiftLeft 3)])
	(let ([shiftRight2 (repeat shiftRight 2)])
	  (if (checkEq ((compose shiftRight2 (compose shiftLeft3 shiftLeft3)) v1)
				   ((compose (repeat shiftLeft3 2) (repeat shiftRight2 2)) v2))
		88
		99)))))
