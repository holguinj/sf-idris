module Main

%default total

data Natprod : Type where
     Pair : Nat -> Nat -> Natprod

fst : (p : Natprod) -> Nat
fst (Pair k _) = k

snd : Natprod -> Nat
snd (Pair _ j) = j

swap_pair : Natprod -> Natprod
swap_pair (Pair k j) = (Pair j k)

surjective_pairing : (p : Natprod) -> p = Pair (fst p) (snd p)
surjective_pairing (Pair k j) = ?surjective_pairing_rhs_1

snd_fst_is_swap : (p : Natprod) -> swap_pair p = Pair (snd p) (fst p)
snd_fst_is_swap (Pair k j) = ?snd_fst_is_swap_rhs_1

data Natlist : Type where
     Nil  : Natlist
     (::) : (x : Nat) -> (xs : Natlist) -> Natlist

repeat : (n : Nat) -> (count : Nat) -> Natlist
repeat n Z = Nil
repeat n (S count') = n :: repeat n count'

length : Natlist -> Nat
length [] = Z
length (k :: xs) = S $ length xs

app : Natlist -> Natlist -> Natlist
app [] l2 = l2
app (x :: xs) l2 = x :: app xs l2

(++) : Natlist -> Natlist -> Natlist
(++) = app

test_app1 : [1, 2, 3] ++ [4, 5, 6] = the Natlist [1, 2, 3, 4, 5, 6]
test_app1 = Refl

test_app2 : Nil ++ [4, 5] = the Natlist [4, 5]
test_app2 = Refl

test_app3 : [1, 2, 3] ++ Nil = the Natlist [1, 2, 3]
test_app3 = Refl

--head with default
hd : (notfound : Nat) -> (l : Natlist) -> Nat
hd notfound [] = notfound
hd _ (x :: _) = x

test_hd1 : hd 0 [1, 2, 3] = 1
test_hd1 = Refl

test_hd2 : hd 0 [] = 0
test_hd2 = Refl

tl : Natlist -> Natlist
tl [] = []
tl (_ :: xs) = xs

test_tl : tl [1, 2, 3] = [2, 3]
test_tl = Refl

nonzeros : Natlist -> Natlist
nonzeros [] = []
nonzeros (x :: xs) = case x of
                          Z => nonzeros xs
                          n => n :: nonzeros xs

test_nonzeros : nonzeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3]
test_nonzeros = Refl

negb : (b : Bool) -> Bool
negb b = case b of
              True => False
              False => True

evenb : (n : Nat) -> Bool
evenb n = case n of
               Z => True
               S Z => False
               S (S n') => evenb n'

oddb : (n : Nat) -> Bool
oddb = negb . evenb

oddmembers : Natlist -> Natlist
oddmembers [] = []
oddmembers (x :: xs) = case oddb x of
                            False => oddmembers xs
                            True => x :: oddmembers xs

test_oddmembers : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3]
test_oddmembers = Refl

countoddmembers : Natlist -> Nat
countoddmembers [] = Z
countoddmembers (x :: xs) = case oddb x of
                                 False => countoddmembers xs
                                 True => S $ countoddmembers xs

test_countoddmembers1 : countoddmembers [0, 2, 4] = 0
test_countoddmembers1 = Refl

test_countoddmembers2 : countoddmembers Nil = 0
test_countoddmembers2 = Refl

test_countoddmembers3 : countoddmembers [1, 0, 3, 1, 4, 5] = 4
test_countoddmembers3 = Refl

Bag : Type
Bag = Natlist

count : (v : Nat) -> (s : Bag) -> Nat
count v [] = Z
count v (x :: xs) = case x == v of
                         False => count v xs
                         True => S $ count v xs

test_count1 : count 1 [1, 2, 3, 1, 4, 1] = 3
test_count1 = Refl

test_count2 : count 6 [1, 2, 3, 1, 4, 1] = 0
test_count2 = Refl

sum : Bag -> Bag -> Bag
sum = app

test_sum1 : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3
test_sum1 = Refl

add : Nat -> Bag -> Bag
add = (::)

member : (v : Nat) -> (s : Bag) -> Bool
member v [] = False
member v (x :: xs) = case v == x of
                          False => member v xs
                          True => True

test_member1 : member 1 [1, 4, 1] = True
test_member1 = Refl

test_member2 : member 2 [1, 4, 1] = False
test_member2 = Refl

remove_one : (v : Nat) -> (s : Bag) -> Bag
remove_one v [] = []
remove_one v (x :: xs) = case v == x of
                              False => x :: remove_one v xs
                              True => xs

test_remove_one1 : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0
test_remove_one1 = Refl

remove_all : (v : Nat) -> (s : Bag) -> Bag
remove_all v [] = []
remove_all v (x :: xs) = case v == x of
                              False => x :: remove_all v xs
                              True => remove_all v xs

test_remove_all1 : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0
test_remove_all1 = Refl

test_remove_all3 : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2
test_remove_all3 = Refl

subset : (s1 : Bag) -> (s2 : Bag) -> Bool
subset [] s2 = True
subset (x :: xs) s2 = case member x s2 of
                           False => False
                           True => subset xs $ remove_one x s2

test_subset1 : subset [1, 2] [2, 1, 4, 1] = True
test_subset1 = Refl

test_subset2 : subset [1, 2, 2] [2, 1, 4, 1] = False
test_subset2 = Refl

count_empty : (n : Nat) -> count n [] = 0
count_empty = ?count_empty1

add_empty : (n : Nat) -> add n [] = [n]
add_empty n = Refl

add_count_empty : (n : Nat) -> count n $ add n [] = 1
add_count_empty n = ?add_count_empty_rhs


bag_theorem : (n : Nat) ->
              (s : Bag) ->
              count n $ add n s = S $ count n s
bag_theorem n [] = ?bag_theorem_empty
bag_theorem n (x :: xs) = ?bag_theorem_nonempty

---------- Proofs ----------

Main.count_empty1 = proof
  intros
  trivial


Main.snd_fst_is_swap_rhs_1 = proof
  intros
  trivial


Main.surjective_pairing_rhs_1 = proof
  intros
  trivial


