(let ((x (if (let ((x 3))
			   (let ((y x))
				 (>= (+ x y) 6)))
			 10
			 5)))
  (let ((z 10))
	(let ((y x))
	  (+ x (+ y z)))))
