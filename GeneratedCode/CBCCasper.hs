{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CBCCasper(Message, Set, is_future_state) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Num = One | Bit0 Num | Bit1 Num;

data Int = Zero_int | Pos Num | Neg Num;

newtype Consensus_value = Consensus_value Int;

newtype Validator = Validator Int;

newtype Message = Message (Consensus_value, (Validator, [Message]));

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

equal_consensus_value :: Consensus_value -> Consensus_value -> Bool;
equal_consensus_value (Consensus_value x) (Consensus_value ya) = equal_int x ya;

instance Eq Consensus_value where {
  a == b = equal_consensus_value a b;
};

equal_validator :: Validator -> Validator -> Bool;
equal_validator (Validator x) (Validator ya) = equal_int x ya;

instance Eq Validator where {
  a == b = equal_validator a b;
};

instance Eq Message where {
  a == b = equal_message a b;
};

equal_message :: Message -> Message -> Bool;
equal_message (Message x) (Message ya) = x == ya;

data Set a = Set [a] | Coset [a];

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

is_future_state :: (Set Message, Set Message) -> Bool;
is_future_state (sigma_1, sigma_2) = less_eq_set sigma_2 sigma_1;

}
