theory CBCCasper

imports Main HOL.Real

begin

(* Section 2: Description of CBC Casper *)
(* Section 2.1: CBC Casper "Parameters" *)

notation Set.empty ("\<emptyset>")

definition is_non_empty :: "'a set \<Rightarrow> bool"
  where
    "is_non_empty bs = ( \<exists> b. b \<in> bs )"

(* Definition 2.1 ~ 2.5 *)
datatype validator = Validator int

type_synonym weight = "validator \<Rightarrow> real"

type_synonym threshold = real

datatype consensus_value = Consensus_value int

(* NOTE: list is used here because set can not be used for recursive definition. *)
datatype message =
  Message "consensus_value * validator * message list"

type_synonym state = "message set"

type_synonym estimator = "state \<Rightarrow> consensus_value set"

(* NOTE: Estimator is parameterized by weight. *)
type_synonym estimator_param = "weight \<Rightarrow> estimator"

(* CBC Casper parameters *)
datatype params = 
  Params "validator set * weight * threshold * consensus_value set * estimator_param"

fun V :: "params \<Rightarrow> validator set"
  where
    "V (Params (v_set, _, _, _, _)) = v_set"

fun W :: "params \<Rightarrow> weight"
  where
    "W (Params (_, w, _, _, _)) = w"

fun t :: "params \<Rightarrow> threshold"
  where
    "t (Params (_, _, threshold, _, _)) = threshold"

fun C :: "params \<Rightarrow> consensus_value set"
  where
    "C (Params (_, _, _, c_set, _)) = c_set"

fun \<epsilon> :: "params \<Rightarrow> estimator"
  where
    "\<epsilon> (Params (_, w, _, _, e)) = e w"


(* Section 2.2: Protocol Definition *)

(* Definition 2.6 *)
fun sender :: "message \<Rightarrow> validator"
  where
    "sender (Message (_, v, _)) = v"

fun est :: "message \<Rightarrow> consensus_value"
  where
     "est (Message (c, _, _)) = c"

fun justification :: "message \<Rightarrow> state"
  where
    "justification (Message (_, _, s)) = set s"

(* Definition 2.7 *)
definition is_valid_message :: "params \<Rightarrow> message \<Rightarrow> bool"
  where
    "is_valid_message params m = (est m \<in> \<epsilon> params (justification m))"

fun M :: "params \<Rightarrow> message set"
  where
    "M params = {m. is_valid_message params m}"

definition is_valid_state :: "params \<Rightarrow> state \<Rightarrow> bool"
  where
    "is_valid_state params \<sigma> = (\<forall> m \<in> \<sigma>. is_valid_message params m)"

fun \<Sigma> :: "params \<Rightarrow> state set"
  where
    "\<Sigma> params = {\<sigma>. is_valid_state params \<sigma>}"

(* Definition 2.1 ~ 2.5 *)
definition is_valid_validators :: "params \<Rightarrow> bool"
  where
     "is_valid_validators params = (is_non_empty (V params))"

definition is_valid_weight :: "params \<Rightarrow> bool"
  where
    "is_valid_weight params = (\<forall> v \<in> V params. 0 \<le> W params v)"

definition is_valid_threshold :: "params \<Rightarrow> bool"
  where
    "is_valid_threshold params = (0 \<le> t params \<and> t params < sum (W params) (V params))"

definition is_valid_consensus_values :: "params \<Rightarrow> bool"
  where
     "is_valid_consensus_values params = (card (C params) > 1)"

definition is_valid_estimator :: "params \<Rightarrow> bool"
  where
    "is_valid_estimator params = (\<forall> \<sigma> \<in> \<Sigma> params. is_non_empty (\<epsilon> params \<sigma>) \<and> \<epsilon> params \<sigma> \<subseteq> C params)"

definition is_valid_params :: "params \<Rightarrow> bool"
  where
    "is_valid_params params = (
      is_valid_validators params
      \<and> is_valid_weight params
      \<and> is_valid_threshold params
      \<and> is_valid_consensus_values params
      \<and> is_valid_estimator params)"

lemma estimates_are_valid:
  "\<forall> params \<sigma> c. is_valid_params params \<and> \<sigma> \<in> \<Sigma> params \<and> c \<in> \<epsilon> params \<sigma> \<longrightarrow> c \<in> C params"
  using is_valid_params_def is_valid_estimator_def
  by blast

(* Definition 2.8: Protocol state transitions \<rightarrow> *)
fun is_future_state :: "(state * state) \<Rightarrow> bool"
  where
    "is_future_state (\<sigma>1, \<sigma>2) = (\<sigma>1 \<supseteq> \<sigma>2)"

(* Definition 2.9 *)
fun equivocation :: "(message * message) \<Rightarrow> bool"
  where
    "equivocation (m1, m2) =
      (sender m1 = sender m2 \<and> m1 \<noteq> m2 \<and> m1 \<notin> justification m2 \<and> m2 \<notin> justification m1)"

(* Definition 2.10 *)
definition equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators \<sigma> = 
      {v. \<exists> m1 m2. m1 \<in> \<sigma> \<and> m2 \<in> \<sigma> \<and> equivocation (m1, m2) \<and> sender m1 = v}"

(* Definition 2.11 *)
definition equivocation_fault_weight :: "params \<Rightarrow> state \<Rightarrow> real"
  where
    "equivocation_fault_weight params \<sigma> = sum (W params) (equivocating_validators \<sigma>)"

(* Definition 2.12 *)
definition is_faults_lt_threshold :: "params \<Rightarrow> state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold params \<sigma> = (equivocation_fault_weight params \<sigma> < t params)"

fun \<Sigma>t :: "params \<Rightarrow> state set"
  where
    "\<Sigma>t params = {\<sigma>. is_valid_state params \<sigma> \<and> is_faults_lt_threshold params \<sigma>}"


end
