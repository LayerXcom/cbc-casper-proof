{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SafetyOracle(Validator, Message, Set, equivocation, is_future_state)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Consensus_value;

data Validator;

newtype Message = Message (Consensus_value, (Validator, [Message]));

instance Eq Message where {
  a == b = equal_message a b;
};

equal_message :: Message -> Message -> bool;
equal_message (Message x) (Message ya) = x == ya;

data Set a = Set [a] | Coset [a];

membera :: forall a. (Eq a) => [a] -> a -> bool;
membera [] y = false;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

sender :: Message -> Validator;
sender (Message (uu, (v, uv))) = v;

equal_validator :: Validator -> Validator -> bool;
equal_validator x y = equal_validator x y;

justification :: Message -> Set Message;
justification (Message (uu, (uv, s))) = Set s;

equivocation :: (Message, Message) -> bool;
equivocation (m1, m2) =
  equal_validator (sender m1) (sender m2) &&
    not (equal_message m1 m2) &&
      not (member m1 (justification m2)) && not (member m2 (justification m1));

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> bool;
less_eq_set (Coset []) (Set []) = false;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

is_future_state :: (Set Message, Set Message) -> bool;
is_future_state (sigma_1, sigma_2) = less_eq_set sigma_2 sigma_1;

}
