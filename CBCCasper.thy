theory CBCCasper

imports Main HOL.Real

begin

(* Section 2: Description of CBC Casper *)
(* Section 2.1: CBC Casper "Parameters" *)

notation Set.empty ("\<emptyset>")

(* Definition 2.1 ~ 2.5 *)
typedecl validator

type_synonym weight = "validator \<Rightarrow> real"

type_synonym threshold = real

typedecl consensus_value

(* NOTE: list is used here because set can not be used for recursive definition. *)
datatype message =
  Message "consensus_value * validator * message list"

type_synonym state = "message set"

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

record params =
  V :: "validator set"
  W :: weight
  t :: threshold
  C :: "consensus_value set"
  \<epsilon> :: "message set \<Rightarrow> consensus_value set"

locale Protocol =
  fixes params :: "'p params_scheme" (structure)
  and \<Sigma> :: "state set"
  and M :: "message set"

  assumes W_type: "\<And>w. w \<in> range (W params) \<Longrightarrow> w > 0"
  and threshould_type: "0 \<le> t params" "t params < Sum (W params ` V params)"
  and estimator_type: "\<And>s. s \<in> \<Sigma> \<Longrightarrow> \<epsilon> params s \<in> Pow (C params) - \<emptyset>"

  assumes \<Sigma>_type: "\<Sigma> \<subseteq> {s. s \<in> Pow M \<and> finite s}"
  and M_type: "\<And>m. m \<in> M \<Longrightarrow> est m \<in> C params \<and> sender m \<in> V params \<and> justification m \<in> \<Sigma>"

(* \<Sigma>, M Construction *)

fun 
  \<Sigma>_i :: "params \<Rightarrow> nat \<Rightarrow> state set" and
  M_i :: "params \<Rightarrow> nat \<Rightarrow> message set"
  where 
    "\<Sigma>_i params 0 = {\<emptyset>}"
  | "\<Sigma>_i params n = {\<sigma> \<in> Pow (M_i params (n - 1)). \<forall> m. m \<in> \<sigma> \<longrightarrow> justification m \<subseteq> \<sigma>}"
  | "M_i params n = {m. est m \<in> C params \<and> sender m \<in> V params \<and> justification m \<in> (\<Sigma>_i params n) \<and> est m \<in> \<epsilon> params (justification m)}" 

fun Mc :: "params \<Rightarrow> message set"
  where
    "Mc params = (\<Union>i\<in>\<nat>. M_i params i)"

fun \<Sigma>c :: "params \<Rightarrow> state set"
  where
    "\<Sigma>c params = (\<Union>i\<in>\<nat>. \<Sigma>_i params i)"

lemma ConstructiveProtocol:
  assumes W_type: "\<And>w. w \<in> range (W params) \<Longrightarrow> w > 0"
  and threshould_type: "0 \<le> t params" "t params < Sum (W params ` V params)"
  and estimator_type: "\<And>s. s \<in> \<Sigma>c params \<Longrightarrow> \<epsilon> params s \<in> Pow (C params) - \<emptyset>"
  shows "Protocol params (\<Sigma>c params) (Mc params)"
  unfolding Protocol_def
  apply rule+
  apply (simp add: W_type)
  apply (simp add: threshould_type)
  apply rule
  using estimator_type apply auto[1]
  apply rule
  defer
  apply simp
(*
statement: \<Sigma>c params \<subseteq> {s \<in> Pow (Mc params). finite s}
\<Sigma>c = \<Union>\<Sigma>i = \<Sigma>0 \<union> \<Union>\<Sigma>(n+1)
   \<subseteq> {\<emptyset>} \<union> \<Union>Pfin Mn
   \<subseteq> \<Union>Pfin Mn  \<leftarrow> ?
*)
  sorry

(* Definition 2.1 ~ 2.5 *)
definition (in Protocol) is_valid_validators :: "bool"
  where
     "is_valid_validators = (V params \<noteq> \<emptyset>)"

definition (in Protocol) is_valid_weight :: "bool"
  where
    "is_valid_weight = (\<forall> v \<in> V params. 0 \<le> W params v)"

definition (in Protocol) is_valid_threshold :: "bool"
  where
    "is_valid_threshold = (0 \<le> t params \<and> t params < sum (W params) (V params))"

definition (in Protocol) is_valid_consensus_values :: "bool"
  where
     "is_valid_consensus_values = (card (C params) > 1)"

definition (in Protocol) is_valid_estimator :: "bool"
  where
    "is_valid_estimator = (\<forall> \<sigma> \<in> \<Sigma>. \<epsilon> params \<sigma> \<in> Pow (C params) - {\<emptyset>})"

definition (in Protocol) is_valid_params :: "bool"
  where
    "is_valid_params = (
      is_valid_validators
      \<and> is_valid_weight
      \<and> is_valid_threshold
      \<and> is_valid_consensus_values
      \<and> is_valid_estimator)"

lemma (in Protocol) estimate_is_valid:
  "\<forall>\<sigma>. is_valid_params \<and> \<sigma> \<in> \<Sigma>
  \<longrightarrow> (\<forall> c \<in> \<epsilon> params \<sigma>. c \<in> C params)"
  using is_valid_params_def is_valid_estimator_def
  by blast

lemma (in Protocol) estimates_are_non_empty:
  "\<forall>\<sigma>. is_valid_params \<and> \<sigma> \<in> \<Sigma>
  \<longrightarrow> \<epsilon> params \<sigma> \<noteq> \<emptyset>"
  using is_valid_params_def is_valid_estimator_def
  by blast

lemma (in Protocol) \<Sigma>_is_non_empty :
  "is_valid_params \<longrightarrow> \<Sigma> \<noteq> \<emptyset>"
  oops

(* NOTE: Issue #32 *)
lemma (in Protocol) \<Sigma>_is_infinite :
  "is_valid_params \<longrightarrow> infinite \<Sigma>"
  oops

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
definition (in Protocol) equivocation_fault_weight :: "state \<Rightarrow> real"
  where
    "equivocation_fault_weight \<sigma> = sum (W params) (equivocating_validators \<sigma>)"

(* Definition 2.12 *)
definition (in Protocol) is_faults_lt_threshold :: "state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold \<sigma> = (equivocation_fault_weight \<sigma> < t params)"

definition (in Protocol) \<Sigma>t :: "state set"
  where
    "\<Sigma>t = {\<sigma> \<in> \<Sigma>. is_faults_lt_threshold \<sigma>}"


end
