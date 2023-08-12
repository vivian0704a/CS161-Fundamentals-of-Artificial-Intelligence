;;Name: Yu-Wei Chen; UID: 205928946

;;;;;;;;;;;;;;
; Homework 2 ;
;;;;;;;;;;;;;;

;;;;;;;;;;;;;;
; Question 1 ;
;;;;;;;;;;;;;;

; TODO: comment code
(defun DFSRL (FRINGE) 
    (cond ((not FRINGE) NIL) ;if the list is empty, return nil
        ((atom FRINGE) (list FRINGE)) ;if the search tree contains a single leaf node then return the node
        (t (append (DFSRL (cdr FRINGE)) (DFSRL (car FRINGE)))))) ;the list is visited form right-to-left, 
                                                                 ;so we recursively call the function from the end of the list and concatenate the results.


;;;;;;;;;;;;;;
; Question 2 ;
;;;;;;;;;;;;;;


; These functions implement a depth-first solver for the homer-baby-dog-poison
; problem. In this implementation, a state is represented by a single list
; (homer baby dog poison), where each variable is T if the respective entity is
; on the west side of the river, and NIL if it is on the east side.
; Thus, the initial state for this problem is (NIL NIL NIL NIL) (everybody 
; is on the east side) and the goal state is (T T T T).

; The main entry point for this solver is the function DFS, which is called
; with (a) the state to search from and (b) the path to this state. It returns
; the complete path from the initial state to the goal state: this path is a
; list of intermediate problem states. The first element of the path is the
; initial state and the last element is the goal state. Each intermediate state
; is the state that results from applying the appropriate operator to the
; preceding state. If there is no solution, DFS returns NIL.
; To call DFS to solve the original problem, one would call 
; (DFS '(NIL NIL NIL NIL) NIL) 
; However, it should be possible to call DFS with a different initial
; state or with an initial path.

; First, we define the helper functions of DFS.

; FINAL-STATE takes a single argument S, the current state, and returns T if it
; is the goal state (T T T T) and NIL otherwise.
(defun FINAL-STATE (S)
    (equal S '(T T T T))) ;compare the current state "S" to final state '(T T T T) and check if they match

; NEXT-STATE returns the state that results from applying an operator to the
; current state. It takes three arguments: the current state (S), and which entity
; to move (A, equal to h for homer only, b for homer with baby, d for homer 
; with dog, and p for homer with poison). 
; It returns a list containing the state that results from that move.
; If applying this operator results in an invalid state (because the dog and baby,
; or poisoin and baby are left unsupervised on one side of the river), or when the
; action is impossible (homer is not on the same side as the entity) it returns NIL.
; NOTE that next-state returns a list containing the successor state (which is
; itself a list); the return should look something like ((NIL NIL T T)).

;to identify the position of each character more directly, we have "car S"= homer; "cadr S"= baby; "caddr S"= dog; "cadddr S"= poison
(defun NEXT-STATE (S A)
    (cond ((equal A "h")                                                
        (if (or (equal (cadr S) (caddr S)) (equal (cadr S) (cadddr S))) ;moving homer, we can't leave baby on the same side as dog or poison
        NIL                                                             ;return nil if baby and dog or poison are on the same side
        (list (cons (not (car S)) (cdr S)))))                           ;or we can change only homer's position
    ((equal A "b") 
        (if (not (equal (car S) (cadr S)))  ;homer is taking baby, so if they are not on the same side return NIL
        NIL
        (list (cons (not (car S)) (cons (not (cadr S)) (cons (caddr S) (cons (cadddr S) NIL))))))) ;or we can change both homer's and baby's positions
    ((equal A "d")
        (if (or (equal (cadr S) (cadddr S)) (not (equal (car S) (caddr S)))) 
        NIL ;homer can't take the dog if they are not on the same side or if this leads to the situation where baby and poison are on the same side 
        (list (cons (not (car S)) (cons (cadr S) (cons (not (caddr S)) (cons (cadddr S) NIL))))))) ;or we can change both homer's and dogs's positions
    ((equal A "p") 
        (if (or (equal (cadr S) (caddr S)) (not (equal (car S) (cadddr S))))
        NIL ;homer can't take the poison if they are not on the same side or if this leads to the situation where baby and dog are on the same side 
        (list (cons (not (car S)) (cons (cadr S) (cons (caddr S) (cons (not (cadddr S)) NIL))))))))) ;or we can change both homer's and poison's positions

; SUCC-FN returns all of the possible legal successor states to the current
; state. It takes a single argument (s), which encodes the current state, and
; returns a list of each state that can be reached by applying legal operators
; to the current state.
(defun SUCC-FN (S)
    (append (NEXT-STATE S "h") (NEXT-STATE S "b") (NEXT-STATE S "d") (NEXT-STATE S "p"))) ;check the function NEXT-STATE with all types of actions, 
                                                                                          ;and concatenate the results

; ON-PATH checks whether the current state is on the stack of states visited by
; this depth-first search. It takes two arguments: the current state (S) and the
; stack of states visited by DFS (STATES). It returns T if s is a member of
; states and NIL otherwise.
(defun ON-PATH (S STATES)
    (if (not STATES)
        NIL                             ;return NIL if the state is empty
        (if (equal S (car STATES))
            T                           ;check the first element of STATES, return TRUE if we find it to be the same as S 
            (ON-PATH S (cdr STATES))))) ;if we have not found S yet, recursively search the rest of STATES

; MULT-DFS is a helper function for DFS. It takes two arguments: a list of
; states from the initial state to the current state (PATH), and the legal
; successor states to the last, current state in the PATH (STATES). PATH is a
; first-in first-out list of states; that is, the first element is the initial
; state for the current search and the last element is the most recent state
; explored. MULT-DFS does a depth-first search on each element of STATES in
; turn. If any of those searches reaches the final state, MULT-DFS returns the
; complete path from the initial state to the goal state. Otherwise, it returns
; NIL.
(defun MULT-DFS (STATES PATH)
	(if (not STATES) 
        NIL                                     ;return NIL if the state is empty
        (if (equal (DFS (car STATES) PATH) NIL) ;starting with the first element of STATES, if we can't find a path to the goal state,
            (MULT-DFS (cdr STATES) PATH)        ;run MULT-DFS on the rest of the states to expand the frontier
            (DFS (car STATES) PATH))))          ;or we can run DFS on the state that leads to the goal state and return the complete path

; DFS does a depth first search from a given state to the goal state. It
; takes two arguments: a state (S) and the path from the initial state to S
; (PATH). If S is the initial state in our search, PATH is set to NIL. DFS
; performs a depth-first search starting at the given state. It returns the path
; from the initial state to the goal state, if any, or NIL otherwise. DFS is
; responsible for checking if S is already the goal state, as well as for
; ensuring that the depth-first search does not revisit a node already on the
; search path.
(defun DFS (S PATH)
    (if (ON-PATH S PATH) 
        NIL                 ;return NIL if S already appeared before
        (if (FINAL-STATE S) ;if S is the goal state
            (append PATH (list S)) ;concatenate all the paths that lead to the goal state
            (MULT-DFS (SUCC-FN S) (append PATH (list S)))))) ;or we need to run MULT-DFS for the successor states, with PATH appending with S 
