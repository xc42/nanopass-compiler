(define (f [x : Integer]) : (Vector ( -> Integer) ( -> Void))
  (vector
	(lambda: () : Integer x)
	(lambda: () : Void (set! x (+ 1 x)))))

(let ([counter (f 0)])
  (let ([get (vector-ref counter 0)])
	(let ([inc (vector-ref counter 1)])
	  (begin
		(inc)
		(inc)
		(inc)
		(get)))))
