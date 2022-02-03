(if 
  (let ((x (if (eq? (+ 2 3) 5) 10 0)))
	(let ((y (+ 5 5))) (eq? x y)))
  (let ((x 1)) (+ x 1))
  (let ((y 2)) (- y 2)))
