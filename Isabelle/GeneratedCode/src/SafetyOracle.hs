{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SafetyOracle(Real, Message, Set, is_clique, is_clique_oracle) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Params;

data Num = One | Bit0 Num | Bit1 Num;

equal_num :: Num -> Num -> Bool;
equal_num (Bit0 x2) (Bit1 x3) = False;
equal_num (Bit1 x3) (Bit0 x2) = False;
equal_num One (Bit1 x3) = False;
equal_num (Bit1 x3) One = False;
equal_num One (Bit0 x2) = False;
equal_num (Bit0 x2) One = False;
equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3;
equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2;
equal_num One One = True;

data Int = Zero_int | Pos Num | Neg Num;

equal_int :: Int -> Int -> Bool;
equal_int (Neg k) (Neg l) = equal_num k l;
equal_int (Neg k) (Pos l) = False;
equal_int (Neg k) Zero_int = False;
equal_int (Pos k) (Neg l) = False;
equal_int (Pos k) (Pos l) = equal_num k l;
equal_int (Pos k) Zero_int = False;
equal_int Zero_int (Neg l) = False;
equal_int Zero_int (Pos l) = False;
equal_int Zero_int Zero_int = True;

instance Eq Int where {
  a == b = equal_int a b;
};

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

newtype Rat = Frct (Int, Int);

quotient_of :: Rat -> (Int, Int);
quotient_of (Frct x) = x;

equal_rat :: Rat -> Rat -> Bool;
equal_rat a b = quotient_of a == quotient_of b;

newtype Real = Ratreal Rat;

equal_real :: Real -> Real -> Bool;
equal_real (Ratreal x) (Ratreal y) = equal_rat x y;

instance Eq Real where {
  a == b = equal_real a b;
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

less_eq_num :: Num -> Num -> Bool;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit1 m) One = False;
less_eq_num (Bit0 m) One = False;
less_eq_num One n = True;

less_num :: Num -> Num -> Bool;
less_num (Bit1 m) (Bit0 n) = less_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num One (Bit1 n) = True;
less_num One (Bit0 n) = True;
less_num m One = False;

less_eq_int :: Int -> Int -> Bool;
less_eq_int (Neg k) (Neg l) = less_eq_num l k;
less_eq_int (Neg k) (Pos l) = True;
less_eq_int (Neg k) Zero_int = True;
less_eq_int (Pos k) (Neg l) = False;
less_eq_int (Pos k) (Pos l) = less_eq_num k l;
less_eq_int (Pos k) Zero_int = False;
less_eq_int Zero_int (Neg l) = False;
less_eq_int Zero_int (Pos l) = True;
less_eq_int Zero_int Zero_int = True;

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

of_bool :: forall a. (Zero_neq_one a) => Bool -> a;
of_bool True = one;
of_bool False = zero;

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

less_int :: Int -> Int -> Bool;
less_int (Neg k) (Neg l) = less_num l k;
less_int (Neg k) (Pos l) = True;
less_int (Neg k) Zero_int = True;
less_int (Pos k) (Neg l) = False;
less_int (Pos k) (Pos l) = less_num k l;
less_int (Pos k) Zero_int = False;
less_int Zero_int (Neg l) = False;
less_int Zero_int (Pos l) = True;
less_int Zero_int Zero_int = False;

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

newtype Message = Message
  (Params.ConsensusValue, (Params.Validator, [Message]));

equal_consensus_value :: Params.ConsensusValue -> Params.ConsensusValue -> Bool;
equal_consensus_value x y = equal_consensus_value x y;

instance Eq Params.ConsensusValue where {
  a == b = equal_consensus_value a b;
};

equal_validator :: Params.Validator -> Params.Validator -> Bool;
equal_validator x y = equal_validator x y;

instance Eq Params.Validator where {
  a == b = equal_validator a b;
};

instance Eq Message where {
  a == b = equal_message a b;
};

equal_message :: Message -> Message -> Bool;
equal_message (Message x) (Message ya) = x == ya;

data Set a = Set [a] | Coset [a];

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex (Set xs) p = any p xs;

ball :: forall a. Set a -> (a -> Bool) -> Bool;
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

filtera :: forall a. (a -> Bool) -> Set a -> Set a;
filtera p (Set xs) = Set (filter p xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
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

est :: Message -> Params.ConsensusValue;
est (Message (c, (uu, uv))) = c;

sender :: Message -> Params.Validator;
sender (Message (uu, (v, uv))) = v;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

equal_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
equal_set a b = less_eq_set a b && less_eq_set b a;

from_sender :: (Params.Validator, Set Message) -> Set Message;
from_sender = (\ (v, a) -> filtera (\ m -> equal_validator (sender m) v) a);

bot_set :: forall a. Set a;
bot_set = Set [];

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

justification :: Message -> Set Message;
justification (Message (uu, (uv, s))) = Set s;

justified :: Message -> Message -> Bool;
justified m1 m2 = member m1 (justification m2);

later :: (Message, Set Message) -> Set Message;
later = (\ (m, a) -> filtera (justified m) a);

later_from :: (Message, (Params.Validator, Set Message)) -> Set Message;
later_from =
  (\ (m, (v, sigma)) -> inf_set (later (m, sigma)) (from_sender (v, sigma)));

l_M :: Set Message -> Params.Validator -> Set Message;
l_M sigma v =
  filtera (\ m -> equal_set (later_from (m, (v, sigma))) bot_set)
    (from_sender (v, sigma));

observed :: Set Message -> Set Params.Validator;
observed sigma = image sender sigma;

equivocation :: (Message, Message) -> Bool;
equivocation =
  (\ (m1, m2) ->
    equal_validator (sender m1) (sender m2) &&
      not (equal_message m1 m2) &&
        not (justified m1 m2) && not (justified m2 m1));

is_equivocating :: Set Message -> Params.Validator -> Bool;
is_equivocating sigma v =
  bex sigma
    (\ m1 ->
      bex sigma
        (\ m2 -> equivocation (m1, m2) && equal_validator (sender m1) v));

equivocating_validators :: Set Message -> Set Params.Validator;
equivocating_validators sigma =
  filtera (is_equivocating sigma) (observed sigma);

l_H_M :: Set Message -> Params.Validator -> Set Message;
l_H_M sigma v =
  (if member v (equivocating_validators sigma) then bot_set else l_M sigma v);

l_H_E :: Set Message -> Params.Validator -> Set Params.ConsensusValue;
l_H_E sigma v = image est (l_H_M sigma v);

l_H_J :: Set Message -> Params.Validator -> Set (Set Message);
l_H_J sigma v = image justification (l_H_M sigma v);

minus_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
minus_set a (Coset xs) = Set (filter (\ x -> member x a) xs);
minus_set a (Set xs) = fold remove xs a;

observed_non_equivocating_validators :: Set Message -> Set Params.Validator;
observed_non_equivocating_validators sigma =
  minus_set (observed sigma) (equivocating_validators sigma);

later_disagreeing_messages ::
  (Params.ConsensusValue -> Bool, (Message, (Params.Validator, Set Message))) ->
    Set Message;
later_disagreeing_messages =
  (\ (p, (m, (v, sigma))) ->
    filtera (\ ma -> not (p (est ma))) (later_from (m, (v, sigma))));

is_agreeing ::
  (Params.ConsensusValue -> Bool, (Set Message, Params.Validator)) -> Bool;
is_agreeing = (\ (p, (sigma, v)) -> ball (l_H_E sigma v) p);

is_clique ::
  (Set Params.Validator, (Params.ConsensusValue -> Bool, Set Message)) -> Bool;
is_clique =
  (\ (v_set, (p, sigma)) ->
    ball v_set
      (\ v ->
        member v (observed_non_equivocating_validators sigma) &&
          ball v_set
            (\ va ->
              is_agreeing (p, (the_elem (l_H_J sigma v), va)) &&
                equal_set
                  (later_disagreeing_messages
                    (p, (the_elem (l_H_M (the_elem (l_H_J sigma v)) va),
                          (va, sigma))))
                  bot_set)));

less_rat :: Rat -> Rat -> Bool;
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

less_real :: Real -> Real -> Bool;
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

weight_measure :: (Params.Validator -> Real) -> Set Params.Validator -> Real;
weight_measure w v_set = sum (\ x -> x) (image w v_set);

divide_real :: Real -> Real -> Real;
divide_real (Ratreal x) (Ratreal y) = Ratreal (divide_rat x y);

minus_real :: Real -> Real -> Real;
minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y);

gt_threshold ::
  Set Params.Validator ->
    (Params.Validator -> Real) ->
      Real -> (Set Params.Validator, Set Message) -> Bool;
gt_threshold v w t =
  (\ (v_set, sigma) ->
    less_real
      (minus_real
        (plus_real
          (divide_real (weight_measure w v) (Ratreal (of_int (Pos (Bit0 One)))))
          t)
        (weight_measure w (equivocating_validators sigma)))
      (weight_measure w v_set));

is_clique_oraclea ::
  Set Params.Validator ->
    (Params.Validator -> Real) ->
      Real ->
        (Set Params.Validator, (Set Message, Params.ConsensusValue -> Bool)) ->
          Bool;
is_clique_oraclea v w t =
  (\ (v_set, (sigma, p)) ->
    is_clique (minus_set v_set (equivocating_validators sigma), (p, sigma)) &&
      gt_threshold v w t
        (minus_set v_set (equivocating_validators sigma), sigma));

is_clique_oracle ::
  Set Params.Validator ->
    (Params.Validator -> Real) ->
      Real ->
        (Set Params.Validator, (Set Message, Params.ConsensusValue -> Bool)) ->
          Bool;
is_clique_oracle = is_clique_oraclea;

}
