(struct Counter ([cnt : Integer]) #:mutable)
(struct Handles ([cnter : Counter] 
				 [inc : (Integer -> Integer)] 
				 [dec : (Integer -> Integer)]) #:mutable)

(define (getCounter [init : Integer]) : Handles
  (let* ([cnter (Counter init)]
		 [inc (lambda: ([i : Integer]) : Integer
					   (let* ([cur (Counter-cnt cnter)])
						 (set-Counter-cnt! cnter (+ i cur))
						 (+ i cur)))]
		 [dec (lambda: ([j : Integer]) : Integer
					   (let* ([cur (Counter-cnt cnter)])
						 (set-Counter-cnt! cnter (- cur j))
						 (- cur j)))])
	(Handles cnter inc dec)))


(let* ([h (getCounter -3)]
	   [asst0 (eq? (Counter-cnt (Handles-cnter h)) -3)]
	   [asst1 (eq? ((Handles-inc h) 23) 20)]
	   [asst2 (eq? (Counter-cnt (Handles-cnter h)) 20)]
	   [asst3 (eq? ((Handles-dec h) 12) 8)]
	   [ans (Counter-cnt (Handles-cnter h))])
  (if (and (and asst0 asst1)
	   (and asst2 asst3))
	ans
	243))
