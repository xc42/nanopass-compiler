(define (mapVec [f : (Integer -> Integer)]
				 [v : (Vector Integer Integer)])
  : (Vector Integer Integer)
  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))

(define (add1 [x : Integer]) : Integer
  (+ x 8))

(vector-ref (mapVec add1 (vector 3 41)) 0)
