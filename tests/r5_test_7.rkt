(define (item1 [x1 : Integer] [x2 : Integer]) : ((Integer Integer -> Integer) (Integer Integer Integer -> Integer) -> Integer)
  (lambda: ([f1 : (Integer Integer -> Integer)]
			[f2 : (Integer Integer Integer -> Integer)]) : Integer
		   (f1 x1 x2)))

(define (item2 [y1 : Integer] [y2 : Integer] [y3 : Integer]) : ((Integer Integer -> Integer) (Integer Integer Integer -> Integer) -> Integer)
  (lambda: ([g1 : (Integer Integer -> Integer)]
			[g2 : (Integer Integer Integer -> Integer)]) : Integer
		   (g2 y1 y2 y3)))


(define (calc [item : ((Integer Integer -> Integer) (Integer Integer Integer -> Integer) -> Integer)]) : Integer
  (item 
	(lambda: ([x_1 : Integer] [x_2 : Integer]) : Integer 
			 (+ x_1 x_2))
	(lambda: ([y_1 : Integer] [y_2 : Integer] [y_3 : Integer]) : Integer 
			 (+ y_1 (+ y_2 y_3)))))


(if (> (read) 0)
  (calc (item1 1 2))
  (calc (item2 3 4 5)))
