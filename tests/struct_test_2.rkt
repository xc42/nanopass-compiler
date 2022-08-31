(struct FnPair ([fst : (Integer -> Integer)]
				[snd : (Integer -> Integer)]) #:mutable)

(let ([pair (FnPair (lambda: ([x : Integer]) : Integer (+ x x))
					(lambda: ([y : Integer]) : Integer (* y y)))])
  ((FnPair-snd pair) ((FnPair-fst pair) 5)))
