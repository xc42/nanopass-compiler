(if (if (if (eq? (- 3 (+ 1 2)) (+ 0 1))
			(eq? (let ((x 2))
				   (let ((y 4))
					 (+ x (- y y))))
				 2)
			#f)
		#t
		#f)
	1
	2)
