(define (dive [v1 : Integer]
			  [v2 : Integer]
			  [v3 : Integer]
			  [v4 : Integer]
			  [v5 : Integer]
			  [v6 : Integer]
			  [v7 : Integer]
			  [v8 : Integer]): (Vector (Vector Integer Integer Integer Integer) (Vector Integer Integer Integer Integer))
  (vector (vector v1 v2 v3 v4) (vector v5 v6 v7 v8)))


(define (zip-with [f : (Integer Integer -> Integer)]
				  [vec1 : (Vector Integer Integer Integer)]
				  [vec2 : (Vector Integer Integer Integer)])
  : (Vector Integer Integer Integer Integer)
  (vector (f (vector-ref vec1 0) (vector-ref vec2 0))
		  (f (vector-ref vec1 1) (vector-ref vec2 1))
		  (f (vector-ref vec1 2) (vector-ref vec2 2))
		  (f (vector-ref vec1 3) (vector-ref vec2 3))))


(define (add x y) (+ x y))

(zip-with add (dive 1 2 3 4 5 6 7 8))
