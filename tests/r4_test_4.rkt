(define (mapVec [f : (Integer -> Integer)]
				 [v : (Vector Integer Integer)])
  : (Vector Integer Integer)
  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))

(define (add8 [x : Integer]) : Integer
  (+ x 8))

(vector-ref (mapVec add8 (vector 3 41)) 0)
