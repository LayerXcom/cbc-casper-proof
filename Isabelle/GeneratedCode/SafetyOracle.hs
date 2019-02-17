{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SafetyOracle(Real, Consensus_value, Validator, Message, Set, is_clique,
                is_clique_oracle)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

one_int :: Int;
one_int = Pos One;

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

class Zero a where {
  zero :: a;
};

instance Zero Int where {
  zero = Zero_int;
};

class (One a, Zero a) => Zero_neq_one a where {
};

instance Zero_neq_one Int where {
};

plus_num :: Num -> Num -> Num;
plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);
plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) One = Bit0 (plus_num m One);
plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n);
plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n);
plus_num (Bit0 m) One = Bit1 m;
plus_num One (Bit1 n) = Bit0 (plus_num n One);
plus_num One (Bit0 n) = Bit1 n;
plus_num One One = Bit0 One;

times_num :: Num -> Num -> Num;
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num One n = n;
times_num m One = m;

times_int :: Int -> Int -> Int;
times_int (Neg m) (Neg n) = Pos (times_num m n);
times_int (Neg m) (Pos n) = Neg (times_num m n);
times_int (Pos m) (Neg n) = Neg (times_num m n);
times_int (Pos m) (Pos n) = Pos (times_num m n);
times_int Zero_int l = Zero_int;
times_int k Zero_int = Zero_int;

uminus_int :: Int -> Int;
uminus_int (Neg m) = Pos m;
uminus_int (Pos m) = Neg m;
uminus_int Zero_int = Zero_int;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

dup :: Int -> Int;
dup (Neg n) = Neg (Bit0 n);
dup (Pos n) = Pos (Bit0 n);
dup Zero_int = Zero_int;

plus_int :: Int -> Int -> Int;
plus_int (Neg m) (Neg n) = Neg (plus_num m n);
plus_int (Neg m) (Pos n) = sub n m;
plus_int (Pos m) (Neg n) = sub m n;
plus_int (Pos m) (Pos n) = Pos (plus_num m n);
plus_int Zero_int l = l;
plus_int k Zero_int = k;

sub :: Num -> Num -> Int;
sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_int;
sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) one_int;
sub (Bit1 m) (Bit1 n) = dup (sub m n);
sub (Bit0 m) (Bit0 n) = dup (sub m n);
sub One (Bit1 n) = Neg (Bit0 n);
sub One (Bit0 n) = Neg (bitM n);
sub (Bit1 m) One = Pos (Bit0 m);
sub (Bit0 m) One = Pos (bitM m);
sub One One = Zero_int;

minus_int :: Int -> Int -> Int;
minus_int (Neg m) (Neg n) = sub n m;
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Pos m) (Pos n) = sub m n;
minus_int Zero_int l = uminus_int l;
minus_int k Zero_int = k;

newtype Rat = Frct (Int, Int);

quotient_of :: Rat -> (Int, Int);
quotient_of (Frct x) = x;

less_eq_num :: Num -> Num -> bool;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit1 m) One = false;
less_eq_num (Bit0 m) One = false;
less_eq_num One n = true;

less_num :: Num -> Num -> bool;
less_num (Bit1 m) (Bit0 n) = less_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num One (Bit1 n) = true;
less_num One (Bit0 n) = true;
less_num m One = false;

less_eq_int :: Int -> Int -> bool;
less_eq_int (Neg k) (Neg l) = less_eq_num l k;
less_eq_int (Neg k) (Pos l) = true;
less_eq_int (Neg k) Zero_int = true;
less_eq_int (Pos k) (Neg l) = false;
less_eq_int (Pos k) (Pos l) = less_eq_num k l;
less_eq_int (Pos k) Zero_int = false;
less_eq_int Zero_int (Neg l) = false;
less_eq_int Zero_int (Pos l) = true;
less_eq_int Zero_int Zero_int = true;

divmod_step_int :: Num -> (Int, Int) -> (Int, Int);
divmod_step_int l (q, r) =
  (if less_eq_int (Pos l) r
    then (plus_int (times_int (Pos (Bit0 One)) q) one_int, minus_int r (Pos l))
    else (times_int (Pos (Bit0 One)) q, r));

divmod_int :: Num -> Num -> (Int, Int);
divmod_int (Bit1 m) (Bit1 n) =
  (if less_num m n then (Zero_int, Pos (Bit1 m))
    else divmod_step_int (Bit1 n) (divmod_int (Bit1 m) (Bit0 (Bit1 n))));
divmod_int (Bit0 m) (Bit1 n) =
  (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
    else divmod_step_int (Bit1 n) (divmod_int (Bit0 m) (Bit0 (Bit1 n))));
divmod_int (Bit1 m) (Bit0 n) =
  (case divmod_int m n of {
    (q, r) -> (q, plus_int (times_int (Pos (Bit0 One)) r) one_int);
  });
divmod_int (Bit0 m) (Bit0 n) = (case divmod_int m n of {
                                 (q, r) -> (q, times_int (Pos (Bit0 One)) r);
                               });
divmod_int One (Bit1 n) = (Zero_int, Pos One);
divmod_int One (Bit0 n) = (Zero_int, Pos One);
divmod_int (Bit1 m) One = (Pos (Bit1 m), Zero_int);
divmod_int (Bit0 m) One = (Pos (Bit0 m), Zero_int);
divmod_int One One = (Pos One, Zero_int);

of_bool :: forall a. (Zero_neq_one a) => bool -> a;
of_bool true = one;
of_bool false = zero;

equal_num :: Num -> Num -> bool;
equal_num (Bit0 x2) (Bit1 x3) = false;
equal_num (Bit1 x3) (Bit0 x2) = false;
equal_num One (Bit1 x3) = false;
equal_num (Bit1 x3) One = false;
equal_num One (Bit0 x2) = false;
equal_num (Bit0 x2) One = false;
equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3;
equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2;
equal_num One One = true;

equal_int :: Int -> Int -> bool;
equal_int (Neg k) (Neg l) = equal_num k l;
equal_int (Neg k) (Pos l) = false;
equal_int (Neg k) Zero_int = false;
equal_int (Pos k) (Neg l) = false;
equal_int (Pos k) (Pos l) = equal_num k l;
equal_int (Pos k) Zero_int = false;
equal_int Zero_int (Neg l) = false;
equal_int Zero_int (Pos l) = false;
equal_int Zero_int Zero_int = true;

adjust_div :: (Int, Int) -> Int;
adjust_div (q, r) = plus_int q (of_bool (not (equal_int r Zero_int)));

divide_int :: Int -> Int -> Int;
divide_int (Neg m) (Neg n) = fst (divmod_int m n);
divide_int (Pos m) (Neg n) = uminus_int (adjust_div (divmod_int m n));
divide_int (Neg m) (Pos n) = uminus_int (adjust_div (divmod_int m n));
divide_int (Pos m) (Pos n) = fst (divmod_int m n);
divide_int k (Neg One) = uminus_int k;
divide_int k (Pos One) = k;
divide_int Zero_int k = Zero_int;
divide_int k Zero_int = Zero_int;

less_int :: Int -> Int -> bool;
less_int (Neg k) (Neg l) = less_num l k;
less_int (Neg k) (Pos l) = true;
less_int (Neg k) Zero_int = true;
less_int (Pos k) (Neg l) = false;
less_int (Pos k) (Pos l) = less_num k l;
less_int (Pos k) Zero_int = false;
less_int Zero_int (Neg l) = false;
less_int Zero_int (Pos l) = true;
less_int Zero_int Zero_int = false;

adjust_mod :: Int -> Int -> Int;
adjust_mod l r = (if equal_int r Zero_int then Zero_int else minus_int l r);

modulo_int :: Int -> Int -> Int;
modulo_int (Neg m) (Neg n) = uminus_int (snd (divmod_int m n));
modulo_int (Pos m) (Neg n) =
  uminus_int (adjust_mod (Pos n) (snd (divmod_int m n)));
modulo_int (Neg m) (Pos n) = adjust_mod (Pos n) (snd (divmod_int m n));
modulo_int (Pos m) (Pos n) = snd (divmod_int m n);
modulo_int k (Neg One) = Zero_int;
modulo_int k (Pos One) = Zero_int;
modulo_int Zero_int k = Zero_int;
modulo_int k Zero_int = k;

abs_int :: Int -> Int;
abs_int i = (if less_int i Zero_int then uminus_int i else i);

gcd_int :: Int -> Int -> Int;
gcd_int k l =
  abs_int
    (if equal_int l Zero_int then k
      else gcd_int l (modulo_int (abs_int k) (abs_int l)));

normalize :: (Int, Int) -> (Int, Int);
normalize p =
  (if less_int Zero_int (snd p)
    then let {
           a = gcd_int (fst p) (snd p);
         } in (divide_int (fst p) a, divide_int (snd p) a)
    else (if equal_int (snd p) Zero_int then (Zero_int, one_int)
           else let {
                  a = uminus_int (gcd_int (fst p) (snd p));
                } in (divide_int (fst p) a, divide_int (snd p) a)));

plus_rat :: Rat -> Rat -> Rat;
plus_rat p q =
  Frct (let {
          a = quotient_of p;
        } in (case a of {
               (aa, c) ->
                 let {
                   b = quotient_of q;
                 } in (case b of {
                        (ba, d) ->
                          normalize
                            (plus_int (times_int aa d) (times_int ba c),
                              times_int c d);
                      });
             }));

newtype Real = Ratreal Rat;

plus_real :: Real -> Real -> Real;
plus_real (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Real where {
  plus = plus_real;
};

zero_rat :: Rat;
zero_rat = Frct (Zero_int, one_int);

zero_real :: Real;
zero_real = Ratreal zero_rat;

instance Zero Real where {
  zero = zero_real;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

instance Semigroup_add Real where {
};

instance Monoid_add Real where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

instance Ab_semigroup_add Real where {
};

instance Comm_monoid_add Real where {
};

data Consensus_value;

data Validator;

newtype Message = Message (Consensus_value, (Validator, [Message]));

instance Eq Message where {
  a == b = equal_message a b;
};

equal_message :: Message -> Message -> bool;
equal_message (Message x) (Message ya) = x == ya;

data Set a = Set [a] | Coset [a];

bex :: forall a. Set a -> (a -> bool) -> bool;
bex (Set xs) p = any p xs;

ball :: forall a. Set a -> (a -> bool) -> bool;
ball (Set xs) p = all p xs;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

of_int :: Int -> Rat;
of_int a = Frct (a, one_int);

filtera :: forall a. (a -> bool) -> Set a -> Set a;
filtera p (Set xs) = Set (filter p xs);

membera :: forall a. (Eq a) => [a] -> a -> bool;
membera [] y = false;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

insert :: forall a. (Eq a) => a -> [a] -> [a];
insert x xs = (if membera xs x then xs else x : xs);

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (insert x xs);
remove x (Set xs) = Set (removeAll x xs);

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

the_elem :: forall a. Set a -> a;
the_elem (Set [x]) = x;

est :: Message -> Consensus_value;
est (Message (c, (uu, uv))) = c;

sender :: Message -> Validator;
sender (Message (uu, (v, uv))) = v;

observed :: Set Message -> Set Validator;
observed sigma = image sender sigma;

justification :: Message -> Set Message;
justification (Message (uu, (uv, s))) = Set s;

justified :: Message -> Message -> bool;
justified m1 m2 = member m1 (justification m2);

later :: (Message, Set Message) -> Set Message;
later = (\ (m, a) -> filtera (justified m) a);

equal_validator :: Validator -> Validator -> bool;
equal_validator x y = equal_validator x y;

equivocation :: (Message, Message) -> bool;
equivocation (m1, m2) =
  equal_validator (sender m1) (sender m2) &&
    not (equal_message m1 m2) &&
      not (member m1 (justification m2)) && not (member m2 (justification m1));

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> bool;
less_eq_set (Coset []) (Set []) = false;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

from_sender :: (Validator, Set Message) -> Set Message;
from_sender = (\ (v, a) -> filtera (\ m -> equal_validator (sender m) v) a);

bot_set :: forall a. Set a;
bot_set = Set [];

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

later_from :: (Message, (Validator, Set Message)) -> Set Message;
later_from =
  (\ (m, (v, sigma)) -> inf_set (later (m, sigma)) (from_sender (v, sigma)));

latest_messages :: Set Message -> Validator -> Set Message;
latest_messages sigma v =
  filtera (\ m -> equal_set (later_from (m, (v, sigma))) bot_set)
    (from_sender (v, sigma));

is_equivocating :: Set Message -> Validator -> bool;
is_equivocating sigma v =
  bex sigma
    (\ m1 ->
      bex sigma
        (\ m2 -> equivocation (m1, m2) && equal_validator (sender m1) v));

latest_messages_from_non_equivocating_validators ::
  Set Message -> Validator -> Set Message;
latest_messages_from_non_equivocating_validators sigma v =
  (if is_equivocating sigma v then bot_set else latest_messages sigma v);

latest_justifications_from_non_equivocating_validators ::
  Set Message -> Validator -> Set (Set Message);
latest_justifications_from_non_equivocating_validators sigma v =
  image justification
    (latest_messages_from_non_equivocating_validators sigma v);

later_disagreeing_messages ::
  (Consensus_value -> bool, (Message, (Validator, Set Message))) -> Set Message;
later_disagreeing_messages (p, (m, (v, sigma))) =
  filtera (\ ma -> not (p (est ma))) (later_from (m, (v, sigma)));

latest_estimates_from_non_equivocating_validators ::
  Set Message -> Validator -> Set Consensus_value;
latest_estimates_from_non_equivocating_validators sigma v =
  image est (latest_messages_from_non_equivocating_validators sigma v);

equivocating_validators :: Set Message -> Set Validator;
equivocating_validators sigma =
  filtera (is_equivocating sigma) (observed sigma);

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);
minus_set a (Set xs) = fold remove xs a;

observed_non_equivocating_validators :: Set Message -> Set Validator;
observed_non_equivocating_validators sigma =
  minus_set (observed sigma) (equivocating_validators sigma);

agreeing_validators :: (Consensus_value -> bool, Set Message) -> Set Validator;
agreeing_validators (p, sigma) =
  filtera
    (\ v -> ball (latest_estimates_from_non_equivocating_validators sigma v) p)
    (observed_non_equivocating_validators sigma);

is_clique :: (Set Validator, (Consensus_value -> bool, Set Message)) -> bool;
is_clique (v_set, (p, sigma)) =
  ball v_set
    (\ v ->
      less_eq_set v_set
        (agreeing_validators
          (p, the_elem
                (latest_justifications_from_non_equivocating_validators sigma
                  v))) &&
        ball v_set
          (\ va ->
            equal_set
              (later_disagreeing_messages
                (p, (the_elem
                       (latest_messages_from_non_equivocating_validators
                         (the_elem
                           (latest_justifications_from_non_equivocating_validators
                             sigma v))
                         va),
                      (va, sigma))))
              bot_set));

less_rat :: Rat -> Rat -> bool;
less_rat p q =
  let {
    a = quotient_of p;
  } in (case a of {
         (aa, c) ->
           let {
             b = quotient_of q;
           } in (case b of {
                  (ba, d) -> less_int (times_int aa d) (times_int c ba);
                });
       });

minus_rat :: Rat -> Rat -> Rat;
minus_rat p q =
  Frct (let {
          a = quotient_of p;
        } in (case a of {
               (aa, c) ->
                 let {
                   b = quotient_of q;
                 } in (case b of {
                        (ba, d) ->
                          normalize
                            (minus_int (times_int aa d) (times_int ba c),
                              times_int c d);
                      });
             }));

less_real :: Real -> Real -> bool;
less_real (Ratreal x) (Ratreal y) = less_rat x y;

divide_rat :: Rat -> Rat -> Rat;
divide_rat p q =
  Frct (let {
          a = quotient_of p;
        } in (case a of {
               (aa, c) ->
                 let {
                   b = quotient_of q;
                 } in (case b of {
                        (ba, d) -> normalize (times_int aa d, times_int c ba);
                      });
             }));

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

sum :: forall a b. (Eq a, Comm_monoid_add b) => (a -> b) -> Set a -> b;
sum g (Set xs) = sum_list (map g (remdups xs));

weight_measure :: (Validator -> Real) -> Set Validator -> Real;
weight_measure w v_set = sum w v_set;

divide_real :: Real -> Real -> Real;
divide_real (Ratreal x) (Ratreal y) = Ratreal (divide_rat x y);

minus_real :: Real -> Real -> Real;
minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y);

gt_threshold ::
  (Validator -> Real) -> Real -> (Set Validator, Set Message) -> bool;
gt_threshold w t (v_set, sigma) =
  less_real
    (minus_real
      (plus_real
        (divide_real (weight_measure w v_set)
          (Ratreal (of_int (Pos (Bit0 One)))))
        t)
      (weight_measure w (equivocating_validators sigma)))
    (weight_measure w v_set);

is_clique_oraclea ::
  (Validator -> Real) ->
    Real -> (Set Validator, (Set Message, Consensus_value -> bool)) -> bool;
is_clique_oraclea w t (v_set, (sigma, p)) =
  is_clique (minus_set v_set (equivocating_validators sigma), (p, sigma)) &&
    gt_threshold w t (minus_set v_set (equivocating_validators sigma), sigma);

is_clique_oracle ::
  (Validator -> Real) ->
    Real -> (Set Validator, (Set Message, Consensus_value -> bool)) -> bool;
is_clique_oracle = is_clique_oraclea;

}
