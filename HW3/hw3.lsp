;Name: Yu-Wei Chen
;UID: 205928946
; CS161 Hw3: Sokoban
; 
; *********************
;    READ THIS FIRST
; ********************* 
;
; All functions that you need to modify are marked with 'EXERCISE' in their header comments.
; Do not modify a-star.lsp.
; This file also contains many helper functions. You may call any of them in your functions.
;
; *Warning*: The provided A* code only supports the maximum cost of 4999 for any node.
; That is f(n)=g(n)+h(n) < 5000. So, be careful when you write your heuristic functions.
; Do not make them return anything too large.
;
; For Allegro Common Lisp users: The free version of Allegro puts a limit on memory.
; So, it may crash on some hard sokoban problems and there is no easy fix (unless you buy 
; Allegro). 
; Of course, other versions of Lisp may also crash if the problem is too hard, but the amount
; of memory available will be relatively more relaxed.
; Improving the quality of the heuristic will mitigate this problem, as it will allow A* to
; solve hard problems with fewer node expansions.
; 
; In either case, this limitation should not significantly affect your grade.
; 
; Remember that most functions are not graded on efficiency (only correctness).
; Efficiency can only influence your heuristic performance in the competition (which will
; affect your score).
;  
;
(defun pq-create ()
  (let ((ans (make-array 5001 :initial-element nil)))
    (setf (aref ans 4999) 0)
    (setf (aref ans 5000) 100000)
    ans))

(defun pq-add (pq my_path new-cost)
  (let ((old-size (aref pq 4999))
        (old-cost (aref pq 5000)))
    (setf (aref pq 4999) (+ 1 old-size))
    (setf (aref pq 5000) (min old-cost new-cost))
    (setf (aref pq new-cost) (cons my_path (aref pq new-cost)))))

(defun pq-lowest-cost (pq start)
  (let ((old-size (aref pq 4999)))
    (cond ((= old-size 0) 100000)
          (t (let ((i start))
            (loop (when (aref pq i) (return i)) (setf i (+ i 1))))))))

(defun pq-remove (pq)
  (let ((old-size (aref pq 4999))
        (old-cost (aref pq 5000)))
    (if (= old-size 0) nil
      (let* ((ans (pop (aref pq old-cost)))
             (new-size (- old-size 1)))
        (setf (aref pq 4999) new-size)
        (setf (aref pq 5000) (pq-lowest-cost pq old-cost))
        ans))))

(defun pq-peek (pq)
  (let ((old-cost (aref pq 5000))
        (old-size (aref pq 4999)))
    (if (= old-size 0) nil
      (first (aref pq old-cost)))))

(defun pq-empty (pq)
  (let ((old-size (aref pq 4999)))
    (= old-size 0)))

;;;;;;;;;;;;;;;;;;;;;;;
;; The hash table for the closed list
;;
;; Lisp hash tables were found to be horrible.  As a result, I defined my
;; own.  This is not a general hash table.  But it will work in conjunction
;; with a*.  It will not grow, so the initial size should be suffiently
;; large.  The ht is a list, where the first element is the size, and the
;; second element is an array of collision lists.  An element in a collision
;; list is a key/value pair.


(defun hash-helper (start l)
  (cond ((null l) start)
        (t (hash-helper (+ (car l) (* start 65559)) (cdr l)))))

(defun hash-fn (s)
  (let ((ans 0))
    (setf ans (hash-helper ans (first s)))
    (setf ans (hash-helper ans (cons 0 nil)))
    (setf ans (hash-helper ans (second s)))
    (setf ans (hash-helper ans (cons 0 nil)))
    (setf ans (hash-helper ans (third s)))
    (setf ans (hash-helper ans (cons 0 nil)))
    (setf ans (hash-helper ans (fourth s)))))

;; Recursive part of myht-get.  Finds the given key and returns its value.

(defvar rcalls 0)
(defvar getcalls 0)

(defun myht-get-r (key collision)
  (incf rcalls)
  (cond ((null collision) nil)
        ((equal (first (first collision)) key) (second (first collision)))
        (t (myht-get-r key (cdr collision)))))

;; Recursive part of myht-remove.  Finds the given key and removes it.
;; Assumes that the key exists.

(defun myht-remove-r (key collision)
  (cond ((equal (first (first collision)) key) (cdr collision))
        (t (cons (car collision) (myht-remove-r key (cdr collision))))))

;; Crreates a ht.

(defun myht-create (size)
  (list size (make-array size :initial-element nil)))

;; Removes the given key, which is assumed to exist.

(defun myht-remove (ht key hash-val)
  (let* ((size (first ht))
         (index (mod hash-val size))
         (collisions (second ht)))
    (setf (aref collisions index)
          (myht-remove-r key (aref collisions index)))))

;; Adds the given key/value pair, assuming the key does not already exist.

(defun myht-add (ht key value hash-val)
  (let* ((size (first ht))
         (index (mod hash-val size))
         (collisions (second ht)))
    (setf (aref collisions index)
          (cons (list key value) (aref collisions index)))))

;; Returns the value corresponding to the given key or nil if key does not
;; exist.
(defun myht-get (ht key hash-val)
  (incf getcalls)
  (let* ((size (first ht))
         (index (mod hash-val size))
         (collisions (second ht)))
    (myht-get-r key (aref collisions index))))
 
;;;;;;;;;;;;;;;;;;;;;;;
;; The A* implementation

(defstruct (my_path)
  "my_path consists of a state, its parent, the cost from the root to the state,
and the total cost of the state (f(n) = g(n) + h(n))"
  state (previous nil) (cost-so-far 0) (total-cost 0))

(defun my_path-states (my_path)
  "collect all the states along this my_path."
  (unless (null my_path)
    (cons (my_path-state my_path)
          (my_path-states (my_path-previous my_path)))))

(defvar expanded 0)
(defvar generated 1)
 
(defun a* (start-state goal-p successor-fn heuristic-fn)
  (setf expanded 0)
  (setf generated 0)
  (setf rcalls 0)
  (setf getcalls 0)
  (let ((open-list (pq-create))
	(closed-list (myht-create 1000000)))
    (pq-add open-list (make-my_path :state start-state) 0)
    (let ((my_path (nreverse
		    (my_path-states
		     (a*-search open-list
				goal-p
				successor-fn
				#'(lambda (x y) (declare (ignore x y)) 1)
				heuristic-fn
				closed-list)))))
      (format t "My_Path: ~A~%" my_path)
      (format t "Nodes Generated by A*: ~A~%" generated)
      (format t "Nodes Expanded by A*: ~A~%" expanded)
      (format t "Solution depth: ~A~%" (- (length my_path) 1))
      (format t "rcalls: ~A~%" rcalls)
      (format t "getcalls: ~A~%" getcalls)
      my_path)))
    
;; find the my_path from start state to a state that satisfies goal-p.
;; Evaluate each state using the sum of cost-fn and remaining-cost-fn.
;; Return the my_path"

(defun a*-search (open-list goal-p successors cost-fn remaining-cost-fn closed-list)
  (loop
     (when (pq-empty open-list) (return nil))
     (when (funcall goal-p (my_path-state (pq-peek open-list)))
       (return (pq-peek open-list)))
     (let* ((my_path (pq-remove open-list))
	    (state (my_path-state my_path))
	    (new-val (my_path-total-cost my_path))
	    (hash-val (hash-fn state))
	    (closed-val (myht-get closed-list state hash-val)))
       (when (or (not closed-val) (< new-val closed-val))
	 (incf expanded)
	 (if closed-val (myht-remove closed-list state hash-val))
	 (myht-add closed-list state new-val hash-val)
	 (dolist (state2 (funcall successors state))
	   (let* ((cost (+ (my_path-cost-so-far my_path)
			   (funcall cost-fn state state2)))
		  (cost2 (funcall remaining-cost-fn state2))
		  (total-cost (+ cost cost2)))
	     (incf generated)
	     (pq-add open-list
		     (make-my_path
		      :state state2 
		      :previous my_path
		      :cost-so-far cost
		      :total-cost total-cost) 
		     total-cost)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; General utility functions
; They are not necessary for this homework.
; Use/modify them for your own convenience.
;
(defun reload()
   (load "C:/Users/Asus/Desktop/hw3.lsp")
  )

;
; For loading a-star.lsp.
;
(defun load-a-star()
   (load "C:/Users/Asus/Desktop/a-star.lsp"))

;
; Reloads hw3.lsp and a-star.lsp
;
(defun reload-all()
  (reload)
  (load-a-star)
  )

;
; A shortcut function.
; goal-test and next-states stay the same throughout the assignment.
; So, you can just call (sokoban <init-state> #'<heuristic-name>).
; 
;
(defun sokoban (s h)
  (a* s #'goal-test #'next-states #'h205928946)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; end general utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We now begin actual Sokoban code
;

; Define some global variables
(setq blank 0)
(setq wall 1)
(setq box 2)
(setq keeper 3)
(setq star 4)
(setq boxstar 5)
(setq keeperstar 6)

; Some helper functions for checking the content of a square
(defun isBlank (v)
  (= v blank)
  )

(defun isWall (v)
  (= v wall)
  )

(defun isBox (v)
  (= v box)
  )

(defun isKeeper (v)
  (= v keeper)
  )

(defun isStar (v)
  (= v star)
  )

(defun isBoxStar (v)
  (= v boxstar)
  )

(defun isKeeperStar (v)
  (= v keeperstar)
  )

;
; Helper function of getKeeperPosition
;
(defun getKeeperColumn (r col)
  (cond ((null r) nil)
	(t (if (or (isKeeper (car r)) (isKeeperStar (car r)))
	       col
	     (getKeeperColumn (cdr r) (+ col 1))
	     );end if
	   );end t
	);end cond
  )

;
; getKeeperPosition (s firstRow)
; Returns a list indicating the position of the keeper (c r).
; 
; Assumes that the keeper is in row >= firstRow.
; The top row is the zeroth row.
; The first (right) column is the zeroth column.
;
(defun getKeeperPosition (s row)
  (cond ((null s) nil)
	(t (let ((x (getKeeperColumn (car s) 0)))
	     (if x
		 ;keeper is in this row
		 (list x row)
		 ;otherwise move on
		 (getKeeperPosition (cdr s) (+ row 1))
		 );end if
	       );end let
	 );end t
	);end cond
  );end defun

;
; cleanUpList (l)
; returns l with any NIL element removed.
; For example, if l is '(1 2 NIL 3 NIL), returns '(1 2 3).
;
(defun cleanUpList (L)
  (cond ((null L) nil)
	(t (let ((cur (car L))
		 (res (cleanUpList (cdr L)))
		 )
	     (if cur 
		 (cons cur res)
		  res
		 )
	     );end let
	   );end t
	);end cond
  );end 

; EXERCISE: Modify this function to return true (t)
; if and only if s is a goal state of a Sokoban game.
; (no box is on a non-goal square)
;
; Currently, it always returns NIL. If A* is called with
; this function as the goal testing function, A* will never
; terminate until the whole search space is exhausted.
;
;helper function for goal-test
(defun outbox (lst)            ;check every list (row) whether there is any box not in the goal
	(cond ((NOT lst) NIL)	   ;if there is no more list or there is no box not in the goal then return nil
	((isBox (car lst)) T)	   ;starting from the fist list, if there is a single box found not to be in the goal, return true
	(t (outbox (cdr lst)))))   ;check rest of the list with recursion
;
(defun goal-test (s)
    (cond ((NOT s) T)          ;return true if there is no more list to check and there's no box not in the goal
	((outbox (car s)) NIL)     ;if there is any box left out of the goal, return nil
	(t (goal-test (cdr s)))))  ;check rest of the list with recursion	

; EXERCISE: Modify this function to return the list of 
; sucessor states of s.
;
; This is the top-level next-states (successor) function.
; Some skeleton code is provided below.
; You may delete them totally, depending on your approach.
; 
; If you want to use it, you will need to set 'result' to be 
; the set of states after moving the keeper in each of the 4 directions.
; A pseudo-code for this is:
; 
; ...
; (result (list (try-move s UP) (try-move s DOWN) (try-move s LEFT) (try-move s RIGHT)))
; ...
; 
; You will need to define the function try-move and decide how to represent UP,DOWN,LEFT,RIGHT.
; Any NIL result returned from try-move can be removed by cleanUpList.

;function to get the content type of a certain cell
(defun conttype (s col row)
	(cond ((or (NOT s) (NOT (car s))) 1)    ;if list is empty, then return value as if it is a wall 
	((or (< row 0) (< col 0)) 1)    ;if there is no boundaries set, the recursion will lead to row or column value<0, set return value as if it is a wall
	((and (= row 0) (= col 0)) (caar s))	;if it is the row and column we are looking for, return the content type 
	((> row 0) (conttype (cdr s) col (- row 1)))  
	((> col 0) (conttype (cons (cdar s) (cdr s)) (- col 1) row))))
    ;if we haven't reached the targeted row or column, recursively search through the rest of the list

;function to set a new content type value to a cell
(defun settype (s col row val)
	(cond ((or (NOT s) (NOT (car s))) s)    ;if there is no more row or column to go through, there is no value needed to be changed, return the original list
	((and (= row 0) (= col 0)) (cons (cons val (cdar s)) (cdr s)))  ; if it is the cell to be altered, return the list with altered value
    ((> row 0) (cons (car s) (settype (cdr s) col (- row 1) val)))
	((> col 0) (cons (cons (caar s) (car (settype (cons (cdar s) (cdr s)) (- col 1) row val))) (cdr (settype (cons (cdar s) (cdr s)) (- col 1) row val))))))
    ;recursively call the settype function if we haven't reached the row and column we want to change

;function try-move changes the cell contents after a possible up, down, left or right move.
(defun try-move(s col row move)
    (cond ((isWall (conttype s col row)) nil)  ;condition 1: if it is a wall then we can't move it
	((isBlank (conttype s col row))    ;condition 2: if it is a blank
	    (cond ((equal move '(UP))      ;if the keeper was at a goal before the move, change the cell to a star after the move
		    (cond ((isKeeperStar (conttype s col (+ row 1))) (settype (settype s col row keeper) col (+ 1 row) star))
		    (t(settype (settype s col row keeper) col (+ 1 row) blank)))) ;if the keeper was at a blank before the move, the cell is blank after the move
	    ((equal move '(DOWN)) 
		    (cond ((isKeeperStar (conttype s col (- row 1))) (settype (settype s col row keeper) col (- row 1) star ))
		    (t(settype (settype s col row keeper) col (- row 1) blank))))
	    ((equal move '(LEFT)) 
		    (cond ((isKeeperStar (conttype s (+ col 1) row)) (settype (settype s col row keeper) (+ col 1) row star ))
		    (t(settype (settype s col row keeper) (+ col 1) row blank))))
        (t (equal move '(RIGHT))
		    (cond ((isKeeperStar (conttype s (- col 1) row)) (settype (settype s col row keeper) (- col 1) row star ))
		    (t(settype (settype s col row keeper) (- col 1) row blank))))))

	((isStar (conttype s col row))    ;condition 3: if it is a star
	    (cond ((equal move '(UP))     ;if the keeper was at a goal before the move, change the cell to a star after the move
            (cond ((isKeeperStar (conttype s col (+ row 1))) (settype (settype s col row keeperstar) col (+ 1 row) star))
            (t(settype (settype s col row keeperstar) col (+ 1 row) blank)))) ;if the keeper was at a blank before the move, the cell is blank after the move
        ((equal move '(DOWN))                                                  ;the keeper ends up on a goal
            (cond ((isKeeperStar (conttype s col (- row 1))) (settype (settype s col row keeperstar) col (- row 1) star ))
            (t(settype (settype s col row keeperstar) col (- row 1) blank))))
        ((equal move '(LEFT))
            (cond ((isKeeperStar (conttype s (+ col 1) row)) (settype (settype s col row keeperstar) (+ col 1) row star ))
            (t(settype (settype s col row keeperstar) (+ col 1) row blank))))
        (t (equal move '(RIGHT))
            (cond ((isKeeperStar (conttype s (- col 1) row)) (settype (settype s col row keeperstar) (- col 1) row star ))
            (t(settype (settype s col row keeperstar) (- col 1) row blank))))))

	((or (isBox (conttype s col row)) (isBoxStar (conttype s col row)))  ;condition 4: if it is a box or box on top of goal
		(cond ((equal move '(UP))    ;if the move is UP: row=row-1
		    (cond ((or (isBox (conttype s col (- row 1))) (isBoxStar (conttype s col (- row 1))) (isWall (conttype s col (- row 1)))) nil) 
			;if the box is next to a box or a wall then we can't move
		    (t (cond ((isBoxStar (conttype s col row))    ;if the box is on the goal
			    (cond ((isKeeperStar (conttype s col (+ row 1))) ;if there is a keeper on the goal below
				    (cond ((isBlank (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) box) col row keeperstar) col (+ 1 row) star))
					;if the cell above the box is blank, we can move the box and set the 3 cells to box, keeperstar, star (up to down)
					    ((isStar (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) boxstar) col row keeperstar)  col (+ 1 row) star))))
					;if the cell above the box is a goal, we can move the box and set the 3 cells to boxstar, keeperstar, star (up to down)	
				    (t (cond ((isBlank (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) box) col row keeperstar) col (+ 1 row) blank))
				    ;if there is the keeper below and the cell above the box is not a goal, move the box and set the 3 cells to box, keeperstar, blank (up to down)
				        ((isStar (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) boxstar) col row keeperstar) col (+ 1 row) blank))))))
			        ;if there is the keeper below and the cell above the box is a goal, move the box and set the 3 cells to boxstar, keeperstar, blank (up to down)
				(t (cond ((isKeeperStar(conttype s col (+ row 1)))
					(cond ((isBlank (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) box) col row keeper) col (+ 1 row) star))
					;if there is the keeper below on a goal and the cell above the box is blank, move the box and set the 3 cells to box, keeper, star (up to down)
					    ((isStar (conttype s  col(- row 1))) (settype (settype (settype s col (- row 1) boxstar) col row keeper) col (+ 1 row) star))))
					;if there is the keeper below on a goal and the cell above the box is a star, move the box and set the 3 cells to boxstar, keeper, star (up to down)
				    (t(cond ((isBlank (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) box) col row keeper) col (+ 1 row) blank))
						;if there is the keeper below not on a goal and the cell above the box is blank, move the box and set the 3 cells to box, keeper, blank (up to down) 
						((isStar (conttype s col (- row 1))) (settype (settype (settype s col (- row 1) boxstar) col row keeper) col (+ 1 row) blank))))))))))
						;if there is the keeper below not on a goal and the cell above the box is a star, move the box and set the 3 cells to boxstar, keeper, blank (up to down)
			                
  
	    ((equal move '(DOWN)) ;if the move is DOWN: row=row+1                                                                                                                  
		    (cond ((or (isBox (conttype s col (+ row 1))) (isBoxStar (conttype s col (+ row 1))) (isWall (conttype s col (+ row 1)))) nil)                                                                                                                   
		    ;if the box is next to a box or a wall then we can't move
			(t (cond ((isBoxStar (conttype s col row)) ;if the box is on the goal
			    (cond ((isKeeperStar (conttype s col (- row 1))) ;if there is a keeper on the goal above                                                                                                    
				    (cond ((isBlank (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) star) col row keeperstar) col (+ row 1) box))
					    ((isStar (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) star) col row keeperstar) col (+ row 1) boxstar))))
                        ;if the row below is blank, moving down will result in star, keeperstar, box
					    ;if the row below is a star, moving down will result in star, keeperstar, boxstar (up to down)
				    (t (cond ((isBlank (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) blank) col row keeperstar) col (+ row 1) box))
				        ((isStar (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) blank) col row keeperstar) col (+ row 1) boxstar))))))
				        ;box on the goal, keeper not on the goal. if the row below is blank, moving down will result in blank, keeperstar, box
				        ;if the row below is a star, moving down will result in blank, keeperstar, boxstar (up to down) 
			    (t (cond ((isKeeperStar (conttype s col (- row 1)))
				    (cond ((isBlank (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) star) col row keeper) col (+ row 1) box))
				        ((isStar (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) star) col row keeper) col (+ row 1) boxstar))))
				    ;box not on the goal, keeper on the goal. if the row below is blank, moving down will result in star, keeper, box
				    ;if the row below is a star, moving down will result in star, keeper, boxstar (up to down)
				    (t (cond ((isBlank (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) blank) col row keeper) col (+ row 1) box))
					    ((isStar (conttype s col (+ row 1))) (settype (settype (settype s col (- row 1) blank) col row keeper) col (+ row 1) boxstar))))))))))
	    			;box not on the goal, keeper not on the goal. if the row below is blank, moving down will result blank, keeper, box
				    ;if the row below is a star, moving down will result in blank, keeper, boxstar (up to down)

	    ((equal move '(LEFT))    ;if the move is LEFT: col=col-1                                                                                                                                                                                   
            (cond ((or (isBox (conttype s (- col 1) row)) (isBoxStar (conttype s (- col 1) row)) (isWall (conttype s (- col 1) row))) nil)
			;if the box is next to a box or a wall then we can't move                                                                                       
		    (t (cond ((isBoxStar (conttype s col row))                                                                                                 
                (cond ((isKeeperStar (conttype s (+ col 1) row))                                                                                                                                                                                                                                                                                                                                      
			        (cond ((isBlank (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row box) col row keeperstar) (+ col 1) row star))
					    ((isStar (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row boxStar) col row keeperstar) (+ col 1) row star))))
					;box on the goal, keeper on the goal. if the left column is blank, moving left will result in box, keeperstar, star
				    ;if the left column is a star, moving left will result in boxstar, keeperstar, star (left to right) 
			        (t(cond ((isBlank (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row box) col row keeperstar) (+ col 1) row blank))
					    ((isStar (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row boxStar) col row keeperstar) (+ col 1) row blank))))))
                    ;box on the goal, keeper not on the goal. if the left column is blank, moving left will result in box, keeperstar, blank
				    ;if the left column is a star, moving left will result in boxstar, keeperstar, blank (left to right)                                                                                                                                                                                      
                (t (cond ((isKeeperStar(conttype s (+ col 1) row))                                                                                             
				    (cond ((isBlank (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row box) col row keeper) (+ col 1) row star))
					((isStar (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row boxStar) col row keeper) (+ col 1) row star))))
                    ;box not on the goal, keeper on the goal. if the left column is blank, moving left will result in box, keeper, star
				    ;if the left column is a star, moving left will result in boxstar, keeper, star (left to right)                                                                                                                                                                        
                    (t(cond ((isBlank (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row box) col row keeper) (+ col 1) row blank))
					((isStar (conttype s (- col 1) row)) (settype (settype (settype s (- col 1) row boxStar) col row keeper) (+ col 1) row blank))))))))))
					;box not on the goal, keeper not on the goal. if the left column is blank, moving left will result in box, keeper, blank
				    ;if the left column is a star, moving left will result in boxstar, keeper, blank (left to right) 

		((equal move '(RIGHT))    ;if the move is RIGHT: col=col+1                                                                                                                                                                                   
		    (cond ((or (isBox(conttype s (+ col 1) row)) (isBoxStar(conttype s (+ col 1) row)) (isWall (conttype s (+ col 1) row))) nil)
			;if the box is next to a box or a wall then we can't move                                                                               
		    (t (cond ((isBoxStar (conttype s col row))                                                                                                     
				(cond ((isKeeperStar (conttype s (- col 1) row))                                                                                                             
				    (cond ((isBlank (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row star) col row keeperstar) (+ col 1) row box))
						((isStar (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row star) col row keeperstar) (+ col 1) row boxStar))))     
					;box on the goal, keeper on the goal. if the right column is blank, moving right will result in star, keeperstar, box
				    ;if the right column is a star, moving right will result in star, keeperstar, boxstar (left to right)                                                                                                                                                                      
				    (t (cond ((isBlank (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row blank) col row keeperstar) (+ col 1) row box))
						((isStar (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row blank) col row keeperstar) (+ col 1) row boxStar))))))                                                                                                                                                                  
					;box on the goal, keeper not on the goal. if the right column is blank, moving right will result in box, keeperstar, blank
				    ;if the right column is a star, moving right will result in blank, keeperstar, boxstar (left to right)     
			    (t (cond ((isKeeperStar (conttype s (- col 1) row))                                                                                                    
					(cond ((isBlank (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row star) col row keeper) (+ col 1) row box))
						((isStar (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row star) col row keeper) (+ col 1) row boxStar))))
                    ;box on the goal, keeper not on the goal. if the right column is blank, moving right will result in star, keeper, box
				    ;if the right column is a star, moving right will result in star, keeper, boxstar (left to right)    
					(t(cond ((isBlank (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row blank) col row keeper) (+ col 1) row box))
						((isStar (conttype s (+ col 1) row)) (settype (settype (settype s (- col 1) row blank) col row keeper) (+ col 1) row boxStar))))))))))))))
					;box on the goal, keeper not on the goal. if the right column is blank, moving right will result in blank, keeper, box
				    ;if the right column is a star, moving right will result in blank, keeper, boxstar (left to right)         
	

(defun next-states (s)
  (let* ((pos (getKeeperPosition s 0))
	 (x (car pos))
	 (y (cadr pos))
	 ;x and y are now the coordinate of the keeper in s.
	 (result (cons (try-move s x (- y 1) '(UP)) (cons (try-move s x (+ 1 y) '(DOWN)) (cons (try-move s (- x 1) y '(LEFT)) (cons (try-move s (+ 1 x) y '(RIGHT)) NIL))))))
	 (cleanUpList result);end
   );end let
  );

; EXERCISE: Modify this function to compute the trivial 
; admissible heuristic.
;
(defun h0 (s)
    0)    ;Write a heuristic function called h0 that returns the constant 0.

; EXERCISE: Modify this function to compute the 
; number of misplaced boxes in s.

;Is this heuristic admissible? 
;Yes because the distance between the box and the goal is not necessarily 1, and the actual distance must take into the additional distances of getting over walls and perhaps boxes that are in the way.
(defun h1 (s)
	(cond ((NOT s) 0)	                ;return 0 if search ends and no misplaced boxes are found
        ((NOT (car s)) (h1 (cdr s)))    ;recursively search each sub-list in s respectively 
		(t (list (car s)) 
		    (cond ((isBox (caar s)) (+ 1 (h1 (cons (cdar s) (cdr s))))) ;if the element we are looking into is a box, add 1 to the total count
			    (h1 (cons (cdar s) (cdr s)))))))                        ;or else continue to search the rest of the list


; EXERCISE: Change the name of this function to h<UID> where
; <UID> is your actual student ID number. Then, modify this 
; function to compute an admissible heuristic value of s. 
; 
; This function will be entered in the competition.
; Objective: make A* solve problems as fast as possible.
; The Lisp 'time' function can be used to measure the 
; running time of a function call.
;---------------------------------------------------------------------
;First, obtain the (row, column) pairs of the location of boxes.
;(Helper finction for boxloc) find where the boxes are in each row:
(defun columns (s n)  
    (cond ((NOT s) NIL)
    ((isBox (car s)) (append (list n) (columns (cdr s) (+ n 1))))
    (t (columns (cdr s) (+ n 1)))))  ;if a box is found, append n to output list, and continue searching the rest of s.
;(Helper finction for boxloc) returns (row, column) pairs of each row
(defun boxhelper (row box)
    (cond ((NOT box) NIL)
    (t (append (list(append (list row) (list(car box)))) (boxhelper row (cdr box))))))

(defun boxloc (s i)        ;search the list for all box locations
    (cond ((NOT s) NIL)    ;if list s is null, return NIL
    (t (append (boxhelper i (columns (car s) 0)) (boxloc (cdr s) (+ i 1)))))) ;return all the (row, column) pairs

;calculates the Manhattan distance between two points (a, b)
(defun distance (a b)
  (+ (abs (- (car a) (car b))) (abs (- (cadr a) (cadr b))))) 

(defun distsum (p boxes)
    (cond ((NOT boxes) 0)    ;if there is no box, no distance needs to be added
    (t (+ (distance p (car boxes)) (distsum p (cdr boxes))))))  ;add up the distances between keeper and each box respectively

;The heuristic calculates the total Manhattan distances between the keeper and each box.
;It is admissible because if the the keeper encounters walls or other boxes, the actual distance will be greater than the Manhattan distance. 
(defun h205928946 (s)
    (distsum (append (list (cadr(getKeeperPosition s 0))) (list (car(getKeeperPosition s 0)))) (boxloc s 0)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
 | Some predefined problems.
 | Each problem can be visualized by calling (printstate <problem>). For example, (printstate p1).
 | Problems are roughly ordered by their difficulties.
 | For most problems, we also privide 2 additional number per problem:
 |    1) # of nodes expanded by A* using our next-states and h0 heuristic.
 |    2) the depth of the optimal solution.
 | These numbers are located at the comments of the problems. For example, the first problem below 
 | was solved by 80 nodes expansion of A* and its optimal solution depth is 7.
 | 
 | Your implementation may not result in the same number of nodes expanded, but it should probably
 | give something in the same ballpark. As for the solution depth, any admissible heuristic must 
 | make A* return an optimal solution. So, the depths of the optimal solutions provided could be used
 | for checking whether your heuristic is admissible.
 |
 | Warning: some problems toward the end are quite hard and could be impossible to solve without a good heuristic!
 | 
 |#

;(80,7)
(setq p1 '((1 1 1 1 1 1)
	   (1 0 3 0 0 1)
	   (1 0 2 0 0 1)
	   (1 1 0 1 1 1)
	   (1 0 0 0 0 1)
	   (1 0 0 0 4 1)
	   (1 1 1 1 1 1)))

;(110,10)
(setq p2 '((1 1 1 1 1 1 1)
	   (1 0 0 0 0 0 1) 
	   (1 0 0 0 0 0 1) 
	   (1 0 0 2 1 4 1) 
	   (1 3 0 0 1 0 1)
	   (1 1 1 1 1 1 1)))

;(211,12)
(setq p3 '((1 1 1 1 1 1 1 1 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 0 0 0 2 0 3 4 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 1 1 1 1 1 1 1 1)))

;(300,13)
(setq p4 '((1 1 1 1 1 1 1)
	   (0 0 0 0 0 1 4)
	   (0 0 0 0 0 0 0)
	   (0 0 1 1 1 0 0)
	   (0 0 1 0 0 0 0)
	   (0 2 1 0 0 0 0)
	   (0 3 1 0 0 0 0)))

;(551,10)
(setq p5 '((1 1 1 1 1 1)
	   (1 1 0 0 1 1)
	   (1 0 0 0 0 1)
	   (1 4 2 2 4 1)
	   (1 0 0 0 0 1)
	   (1 1 3 1 1 1)
	   (1 1 1 1 1 1)))

;(722,12)
(setq p6 '((1 1 1 1 1 1 1 1)
	   (1 0 0 0 0 0 4 1)
	   (1 0 0 0 2 2 3 1)
	   (1 0 0 1 0 0 4 1)
	   (1 1 1 1 1 1 1 1)))

;(1738,50)
(setq p7 '((1 1 1 1 1 1 1 1 1 1)
	   (0 0 1 1 1 1 0 0 0 3)
	   (0 0 0 0 0 1 0 0 0 0)
	   (0 0 0 0 0 1 0 0 1 0)
	   (0 0 1 0 0 1 0 0 1 0)
	   (0 2 1 0 0 0 0 0 1 0)
	   (0 0 1 0 0 0 0 0 1 4)))

;(1763,22)
(setq p8 '((1 1 1 1 1 1)
	   (1 4 0 0 4 1)
	   (1 0 2 2 0 1)
	   (1 2 0 1 0 1)
	   (1 3 0 0 4 1)
	   (1 1 1 1 1 1)))

;(1806,41)
(setq p9 '((1 1 1 1 1 1 1 1 1) 
	   (1 1 1 0 0 1 1 1 1) 
	   (1 0 0 0 0 0 2 0 1) 
	   (1 0 1 0 0 1 2 0 1) 
	   (1 0 4 0 4 1 3 0 1) 
	   (1 1 1 1 1 1 1 1 1)))

;(10082,51)
(setq p10 '((1 1 1 1 1 0 0)
	    (1 0 0 0 1 1 0)
	    (1 3 2 0 0 1 1)
	    (1 1 0 2 0 0 1)
	    (0 1 1 0 2 0 1)
	    (0 0 1 1 0 0 1)
	    (0 0 0 1 1 4 1)
	    (0 0 0 0 1 4 1)
	    (0 0 0 0 1 4 1)
	    (0 0 0 0 1 1 1)))

;(16517,48)
(setq p11 '((1 1 1 1 1 1 1)
	    (1 4 0 0 0 4 1)
	    (1 0 2 2 1 0 1)
	    (1 0 2 0 1 3 1)
	    (1 1 2 0 1 0 1)
	    (1 4 0 0 4 0 1)
	    (1 1 1 1 1 1 1)))

;(22035,38)
(setq p12 '((0 0 0 0 1 1 1 1 1 0 0 0)
	    (1 1 1 1 1 0 0 0 1 1 1 1)
	    (1 0 0 0 2 0 0 0 0 0 0 1)
	    (1 3 0 0 0 0 0 0 0 0 0 1)
	    (1 0 0 0 2 1 1 1 0 0 0 1)
	    (1 0 0 0 0 1 0 1 4 0 4 1)
	    (1 1 1 1 1 1 0 1 1 1 1 1)))

;(26905,28)
(setq p13 '((1 1 1 1 1 1 1 1 1 1)
	    (1 4 0 0 0 0 0 2 0 1)
	    (1 0 2 0 0 0 0 0 4 1)
	    (1 0 3 0 0 0 0 0 2 1)
	    (1 0 0 0 0 0 0 0 0 1)
	    (1 0 0 0 0 0 0 0 4 1)
	    (1 1 1 1 1 1 1 1 1 1)))

;(41715,53)
(setq p14 '((0 0 1 0 0 0 0)
	    (0 2 1 4 0 0 0)
	    (0 2 0 4 0 0 0)	   
	    (3 2 1 1 1 0 0)
	    (0 0 1 4 0 0 0)))

;(48695,44)
(setq p15 '((1 1 1 1 1 1 1)
	    (1 0 0 0 0 0 1)
	    (1 0 0 2 2 0 1)
	    (1 0 2 0 2 3 1)
	    (1 4 4 1 1 1 1)
	    (1 4 4 1 0 0 0)
	    (1 1 1 1 0 0 0)
	    ))

;(91344,111)
(setq p16 '((1 1 1 1 1 0 0 0)
	    (1 0 0 0 1 0 0 0)
	    (1 2 1 0 1 1 1 1)
	    (1 4 0 0 0 0 0 1)
	    (1 0 0 5 0 5 0 1)
	    (1 0 5 0 1 0 1 1)
	    (1 1 1 0 3 0 1 0)
	    (0 0 1 1 1 1 1 0)))

;(3301278,76)
(setq p17 '((1 1 1 1 1 1 1 1 1 1)
	    (1 3 0 0 1 0 0 0 4 1)
	    (1 0 2 0 2 0 0 4 4 1)
	    (1 0 2 2 2 1 1 4 4 1)
	    (1 0 0 0 0 1 1 4 4 1)
	    (1 1 1 1 1 1 0 0 0 0)))

;(??,25)
(setq p18 '((0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1)
	    (0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0)
	    (0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0)
	    (0 0 0 0 0 0 0 0 3 0 0 0 0 0 0 0)
	    (0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0)
	    (0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0)
	    (1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 4 1 0 0 0 0)
	    (0 0 0 0 1 0 2 0 0 0 0 1 0 0 0 0)	    
	    (0 0 0 0 1 0 2 0 0 0 4 1 0 0 0 0)
	    ))
;(??,21)
(setq p19 '((0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (1 1 1 1 0 0 0 0 1 1 1 1)
	    (0 0 0 0 1 0 0 1 0 0 0 0)
	    (0 0 0 0 0 0 3 0 0 0 2 0)
	    (0 0 0 0 1 0 0 1 0 0 0 4)
	    (1 1 1 1 0 0 0 0 1 1 1 1)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 2 0 4 1 0 0 0)))

;(??,??)
(setq p20 '((0 0 0 1 1 1 1 0 0)
	    (1 1 1 1 0 0 1 1 0)
	    (1 0 0 0 2 0 0 1 0)
	    (1 0 0 5 5 5 0 1 0)
	    (1 0 0 4 0 4 0 1 1)
	    (1 1 0 5 0 5 0 0 1)
	    (0 1 1 5 5 5 0 0 1)
	    (0 0 1 0 2 0 1 1 1)
	    (0 0 1 0 3 0 1 0 0)
	    (0 0 1 1 1 1 1 0 0)))

;(??,??)
(setq p21 '((0 0 1 1 1 1 1 1 1 0)
	    (1 1 1 0 0 1 1 1 1 0)
	    (1 0 0 2 0 0 0 1 1 0)
	    (1 3 2 0 2 0 0 0 1 0)
	    (1 1 0 2 0 2 0 0 1 0)
	    (0 1 1 0 2 0 2 0 1 0)
	    (0 0 1 1 0 2 0 0 1 0)
	    (0 0 0 1 1 1 1 0 1 0)
	    (0 0 0 0 1 4 1 0 0 1)
	    (0 0 0 0 1 4 4 4 0 1)
	    (0 0 0 0 1 0 1 4 0 1)
	    (0 0 0 0 1 4 4 4 0 1)
	    (0 0 0 0 1 1 1 1 1 1)))

;(??,??)
(setq p22 '((0 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 0 0 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 0 0 1 2 0 0 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 1 1 1 0 0 2 1 1 0 0 0 0 0 0 0 0 0)
	    (0 0 1 0 0 2 0 2 0 1 0 0 0 0 0 0 0 0 0)
	    (1 1 1 0 1 0 1 1 0 1 0 0 0 1 1 1 1 1 1)
	    (1 0 0 0 1 0 1 1 0 1 1 1 1 1 0 0 4 4 1)
	    (1 0 2 0 0 2 0 0 0 0 0 0 0 0 0 0 4 4 1)
	    (1 1 1 1 1 0 1 1 1 0 1 3 1 1 0 0 4 4 1)
	    (0 0 0 0 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1)
	    (0 0 0 0 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
 | Utility functions for printing states and moves.
 | You do not need to understand any of the functions below this point.
 |#

;
; Helper function of prettyMoves
; from s1 --> s2
;
(defun detectDiff (s1 s2)
  (let* ((k1 (getKeeperPosition s1 0))
	 (k2 (getKeeperPosition s2 0))
	 (deltaX (- (car k2) (car k1)))
	 (deltaY (- (cadr k2) (cadr k1)))
	 )
    (cond ((= deltaX 0) (if (> deltaY 0) 'DOWN 'UP))
	  (t (if (> deltaX 0) 'RIGHT 'LEFT))
	  );end cond
    );end let
  );end defun

;
; Translates a list of states into a list of moves.
; Usage: (prettyMoves (a* <problem> #'goal-test #'next-states #'heuristic))
;
(defun prettyMoves (m)
  (cond ((null m) nil)
	((= 1 (length m)) (list 'END))
	(t (cons (detectDiff (car m) (cadr m)) (prettyMoves (cdr m))))
	);end cond
  );

;
; Print the content of the square to stdout.
;
(defun printSquare (s)
  (cond ((= s blank) (format t " "))
	((= s wall) (format t "#"))
	((= s box) (format t "$"))
	((= s keeper) (format t "@"))
	((= s star) (format t "."))
	((= s boxstar) (format t "*"))
	((= s keeperstar) (format t "+"))
	(t (format t "|"))
	);end cond
  )

;
; Print a row
;
(defun printRow (r)
  (dolist (cur r)
    (printSquare cur)    
    )
  );

;
; Print a state
;
(defun printState (s)
  (progn    
    (dolist (cur s)
      (printRow cur)
      (format t "~%")
      )
    );end progn
  )

;
; Print a list of states with delay.
;
(defun printStates (sl delay)
  (dolist (cur sl)
    (printState cur)
    (sleep delay)
    );end dolist
  );end defun
