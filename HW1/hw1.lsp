;;;Name: Yu-Wei Chen, UID: 205928946

;;Question 1
;;function SEQ takes a single integer argument N (N >= 0), and returns the Nth Padovan number.
(defun SEQ(N)                                          
    (if (<= N 2)                                      
        1                                              ;By definition: SEQ(0) = SEQ(1) = SEQ(2) = 1
        (+ (SEQ(- N 1)) (SEQ(- N 2)) (SEQ(- N 3)))))   ;for N>2, SEQ(N) = SEQ(N-1) + SEQ(N-2) + SEQ(N-3)



;;Question 2
;;function SUMS takes a single numeric argument N, and returns the number of additions required by SEQ to compute the Nth Padovan number.
(defun SUMS(N)
    (if (<= N 2)                                          
        0                                                 ;SEQ(0), SEQ(1), SEQ(2) are predefined.
        (+ (SUMS(- N 1)) (SUMS(- N 2)) (SUMS(- N 3)) 2))) 
        ;for N>2, to generate a new number, we include the number of additions of the prior 3 numbers, plus two additional plus signs to concatenate all the numbers.


;;Question 3
;;function ANON takes a single argument TREE that represents a tree, and returns an anonymized tree 
;;with the same structure, but where all symbols and numbers in the tree are replaced by 0.
(defun ANON(TREE)
    (if (not TREE)
        Nil                                              ;return Nil if the tree is empty
        (if (atom TREE)
            0                                            ;a single leaf node can be represented by atom L. The question requires all symbols and numbers to be replaced by 0.
            (cons (ANON(car TREE)) (ANON(cdr TREE)))))) 
            ;repeatedly take the first element and the remainder of the tree, each let them run until there is only 1 element left and be replaced by 0, 
            ;and concatenate all the subproblem results.
