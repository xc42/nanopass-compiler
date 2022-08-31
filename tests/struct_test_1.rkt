(struct Point ([x : Integer] [y : Integer]) #:mutable)

(define (pointAdd [p1 : Point]
				   [p2 : Point]) : Point
  (Point (+ (Point-x p1) (Point-x p1))
		 (+ (Point-y p2) (Point-y p2))))


(let* ([p1 (Point 3 4)]
	   [p2 (Point 5 6)]
	   [p (pointAdd p1 p2)])
  (+ (Point-x p) (Point-y p)))
