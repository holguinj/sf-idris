module Main

%default total

data Day = Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday


next_weekday : (d : Day) -> Day
next_weekday d =
  case d of
       Monday    => Tuesday
       Tuesday   => Wednesday
       Wednesday => Thursday
       Thursday  => Friday
       Friday    => Saturday
       Saturday  => Sunday
       Sunday    => Monday

next_weekday_ex1 : Wednesday = next_weekday Tuesday
next_weekday_ex1 = Refl

next_weekday_ex2 : Friday = next_weekday $ next_weekday Wednesday
next_weekday_ex2 = Refl

next_weekday_ex3 : Monday = next_weekday $ next_weekday $ next_weekday Friday
next_weekday_ex3 = Refl

negb : (b : Bool) -> Bool
negb b = case b of
               True => False
               False => True

negb_f : True = negb False
negb_f = Refl

negb_t : False = negb True
negb_t = Refl

andb : (b1 : Bool) -> (b2 : Bool) -> Bool
andb b1 b2 = case b1 of
                  True => b2
                  False => False

andb_f1 : False = andb True False
andb_f1 = Refl

andb_f2 : False = andb False True
andb_f2 = Refl

andb_f3 : False = andb False False
andb_f3 = Refl

andb_t : True = andb True True
andb_t = Refl

orb : (b1 : Bool) -> (b2 : Bool) -> Bool
orb b1 b2 = case b1 of
                 True => True
                 False => b2

orb_t1 : True = orb True False
orb_t1 = Refl

orb_t2 : True = orb False True
orb_t2 = Refl

orb_f : False = orb False False
orb_f = Refl

nandb : (b1 : Bool) -> (b2 : Bool) -> Bool
nandb b1 b2 = case (b1, b2) of
                   (True, True) => False
                   _ => True

test_nandb1 : True = (nandb True False)
test_nandb1 = Refl

test_nandb2 : True = (nandb False False)
test_nandb2 = Refl

test_nandb3 : True = (nandb False True)
test_nandb3 = Refl

test_nandb4 : False = (nandb True True)
test_nandb4 = Refl

andb3 : (b1 : Bool) -> (b2 : Bool) -> (b3 : Bool) -> Bool
andb3 b1 b2 b3 = case (b1, b2, b3) of
                      (True, True, True) => True
                      _ => False

test_andb31 : True = (andb3 True True True)
test_andb31 = Refl

test_andb32 : False = (andb3 False True True)
test_andb32 = Refl

test_andb33 : False = (andb3 True False True)
test_andb33 = Refl

test_andb34 : False = (andb3 True True False)
test_andb34 = Refl

pred : (n : Nat) -> Nat
pred Z = Z
pred (S k) = k

minustwo : (n : Nat) -> Nat
minustwo n = case n of
                  Z => Z
                  (S Z) => Z
                  (S (S n')) => n'

evenb : (n : Nat) -> Bool
evenb n = case n of
               Z => True
               S Z => False
               S (S n') => evenb n'

oddb : (n : Nat) -> Bool
oddb = negb . evenb

plusn : (n : Nat) -> (m : Nat) -> Nat
plusn n m = case n of
                Z => m
                S k => S (plusn k m)

multn : (n : Nat) -> (m : Nat) -> Nat
multn n m = case n of
                 Z => Z
                 S k => plusn m (multn k m)

factorial : (n : Nat) -> Nat
factorial Z = (S Z)
factorial (S k) = multn (S k) $ factorial k

test_factorial1 : (factorial 3) = 6
test_factorial1 = Refl

test_factorial2 : (factorial 5) = (multn 10 12)
test_factorial2 = Refl

t_plus_Z_n : (n : Nat) -> plusn 0 n = n
t_plus_Z_n n = Refl

t_plus_1_1 : (n : Nat) -> plusn 1 n = S n
t_plus_1_1 n = Refl

plus_id_example : (n : Nat) ->
                  (m : Nat) ->
                  n = m ->
                  n `plusn` m = m `plusn` n
plus_id_example n m prf = ?plus_id_proof

beq_nat : (n : Nat) -> (m : Nat) -> Bool
beq_nat n m = case n of
                   Z => case m of
                             Z => True
                             S m' => False
                   S n' => case m of
                                Z => False
                                S m' => beq_nat n' m'

plus_1_neq_0 : (n : Nat) ->
               beq_nat (plusn 1 n) 0 = False
plus_1_neq_0 Z = ?plus_2
plus_1_neq_0 (S k) = ?plus_3

total
double_neg : (b : Bool) -> (negb . negb) b = b
double_neg False = Refl
double_neg True = Refl

minus_diag : (n : Nat) -> minus n n = 0
minus_diag n = ?minus_diag_rhs

---------- Proofs ----------

Main.plus_id_proof = proof
  intros
  rewrite prf
  trivial


-- Main.minus_diag_rhs = proof
--   intros
--   induction n
--   trivial
--   intros
--   trivial


Main.plus_2 = proof
  trivial

Main.plus_3 = proof
  intros
  trivial

