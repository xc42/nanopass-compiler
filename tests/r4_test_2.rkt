(define (add4
		  [a1 : Integer]
		  [a2 : Integer]
		  [a3 : Integer]
		  [a4 : Integer]) : Integer
  (+ (+ a1 a2) (+ a3 a4)))

(define (add8 
		  [a1 : Integer]
		  [a2 : Integer]
		  [a3 : Integer]
		  [a4 : Integer]
		  [a5 : Integer]
		  [a6 : Integer]
		  [a7 : Integer]
		  [a8 : Integer]) : Integer
  (+ (add4 a1 a2 a3 a4) (add4 a5 a6 a7 a8)))


(add8 1 2 3 4 5 6 7 8)
