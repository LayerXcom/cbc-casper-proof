theory ConsensusSafety

imports Main

begin

(* Section 2: Description of CBC Casper *)
(* Section 2.1: CBC Casper "Parameters" *)

(* Definition 2.1 *)
datatype validator = Validator int

(* Definition 2.2 *)
type_synonym weight = "validator \<Rightarrow> int"

(* Definition 2.3 *)
type_synonym threshold = int

(* Definition 2.4 *)
datatype consensus_value = Consensus_value int

(* NOTE: list is used here because set can not be used for recursive definition. *)
datatype message =
  Message "consensus_value * validator * message list"

type_synonym state = "message set"

(* Definition 2.5 *)
type_synonym estimator = "state \<Rightarrow> consensus_value set"

(* NOTE: Estimator parameterized by weight. *)
type_synonym estimator_param = "weight \<Rightarrow> state \<Rightarrow> consensus_value set"

(* CBC Casper parameters *)
datatype params = 
  Params "validator set * weight * threshold * consensus_value set * estimator_param"

fun V :: "params \<Rightarrow> validator set"
  where
    "V (Params (v_set, _, _, _, _)) = v_set"

fun W :: "params \<Rightarrow> weight"
  where
    "W (Params (_, weight, _, _, _)) = weight"

fun t :: "params \<Rightarrow> threshold"
  where
    "t (Params (_, _, threshold, _, _)) = threshold"

fun C :: "params \<Rightarrow> consensus_value set"
  where
    "C (Params (_, _, _, c_set, _)) = c_set"

fun \<epsilon> :: "params \<Rightarrow> estimator"
  where
    "\<epsilon> (Params (_, weight, _, _, estimator_param)) = estimator_param weight"


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

definition is_valid_state :: "params \<Rightarrow> state \<Rightarrow> bool"
  where
    "is_valid_state params \<sigma> = (\<forall> m \<in> \<sigma>. is_valid_message params m)"

fun \<Sigma> :: "params \<Rightarrow> state set"
  where
    "\<Sigma> params = {\<sigma>. is_valid_state params \<sigma>}"

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
definition equivocation_fault_weight :: "params \<Rightarrow> state \<Rightarrow> int"
  where
    "equivocation_fault_weight params \<sigma> = sum (W params) (equivocating_validators \<sigma>)"

(* Definition 2.12 *)
definition is_faults_lt_threshold :: "params \<Rightarrow> state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold params \<sigma> = (equivocation_fault_weight params \<sigma> < t params)"

fun \<Sigma>t :: "params \<Rightarrow> state set"
  where
    "\<Sigma>t params = {\<sigma>. is_valid_state params \<sigma> \<and> is_faults_lt_threshold params \<sigma>}"


(* Section 3: Safety Proof *)
(* Section 3.1: Guaranteeing Common Futures *)

(* Definition 3.1 *)
fun futures :: "params \<Rightarrow> state \<Rightarrow> state set"
  where
    "futures params \<sigma> = {\<sigma>'. is_faults_lt_threshold params \<sigma>' \<and> is_future_state (\<sigma>', \<sigma>)}"

(* Lemma 1 *)
lemma monotonic_futures :
  "\<forall> params \<sigma>' \<sigma>. \<sigma>' \<sigma> \<in> \<Sigma>t params
   \<Longrightarrow> (\<sigma>' \<in> futures params \<sigma> \<longleftrightarrow> futures params \<sigma>' \<subseteq> futures params \<sigma>)"
  by fastforce

notation Set.empty ("\<emptyset> ")

(* Theorem 1 *)
theorem two_party_common_futures :
  "\<forall> params \<sigma>1 \<sigma>2. \<sigma>1 \<sigma>2 \<in> \<Sigma>t params
  \<Longrightarrow> is_faults_lt_threshold params (\<sigma>1 \<union> \<sigma>2)
  \<Longrightarrow> futures params \<sigma>1 \<inter> futures params \<sigma>2 \<noteq> \<emptyset>"
  by auto

(* Theorem 2 *)
theorem n_party_common_futures :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<Longrightarrow> is_faults_lt_threshold params (\<Union> \<sigma>_set)
  \<Longrightarrow> futures params \<sigma>1 \<inter> futures params \<sigma>2 \<noteq> \<emptyset>"
  apply (simp add: is_faults_lt_threshold_def)
  by blast


(* Section 3.2: Guaranteeing Consistent Decisions *)
(* Section 3.2.1: Guaranteeing Consistent Decisions on Properties of Protocol States *)

(* Definition 3.2  *)
type_synonym state_property = "state \<Rightarrow> bool"

fun state_property_not :: "state_property \<Rightarrow> state_property"
  where
    "state_property_not p = (\<lambda>\<sigma>. (\<not> p \<sigma>))"

(* Definition 3.3  *)
fun state_property_is_decided :: "params \<Rightarrow> (state_property * state) \<Rightarrow> bool"
  where
    "state_property_is_decided params (p, \<sigma>) = (\<forall> \<sigma>'. \<sigma>' \<in> futures params \<sigma> \<and> p \<sigma>')"

(* Lemma 2 *)
lemma forward_consistency :
  "\<forall> params \<sigma>' \<sigma>. \<sigma>' \<sigma> \<in> \<Sigma>t params
  \<Longrightarrow> \<sigma>' \<in> futures params \<sigma> 
  \<Longrightarrow> state_property_is_decided params (p, \<sigma>)
  \<Longrightarrow> state_property_is_decided params (p, \<sigma>')"
  apply simp
  by (metis W.simps equivocation_fault_weight_def is_faults_lt_threshold_def less_irrefl t.simps) 

(* Lemma 3 *)
lemma backword_consistency :
  "\<forall> params \<sigma>' \<sigma>. \<sigma>' \<sigma> \<in> \<Sigma>t params
  \<Longrightarrow> state_property_is_decided params (p, \<sigma>')
  \<Longrightarrow> \<not>state_property_is_decided params (state_property_not p, \<sigma>)"
  by auto
  
(* Theorem 3 *)
theorem two_party_consensus_safety :
  "\<forall> params \<sigma>1 \<sigma>2. \<sigma>1 \<sigma>2 \<in> \<Sigma>t params
  \<Longrightarrow> is_faults_lt_threshold params (\<sigma>1 \<union> \<sigma>2)
  \<Longrightarrow> \<not>(state_property_is_decided params (p, \<sigma>1) \<and> state_property_is_decided params (state_property_not p, \<sigma>2))"
  by auto

(* Definition 3.4 *)
(* NOTE: We can use \<And> to make it closer to the paper? *)
definition state_properties_are_inconsistent :: "params \<Rightarrow> state_property set \<Rightarrow> bool"
  where
    "state_properties_are_inconsistent params p_set = (\<forall> \<sigma>. \<sigma> \<in> \<Sigma> params \<and> \<not> (\<forall> p. p \<in> p_set \<and> p \<sigma>))"

(* Definition 3.5 *)
definition state_properties_are_consistent :: "params \<Rightarrow> state_property set \<Rightarrow> bool"
  where
    "state_properties_are_consistent params p_set = (\<exists> \<sigma>. \<sigma> \<in> \<Sigma> params \<and> (\<forall> p. p \<in> p_set \<and> p \<sigma>))"

(* Definition 3.6 *)
definition state_property_decisions :: "params \<Rightarrow> state \<Rightarrow> state_property set"
  where 
    "state_property_decisions params \<sigma> = {p. state_property_is_decided params (p, \<sigma>)}"

(* Theorem 4 *)
theorem n_party_safety_for_state_properties :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<Longrightarrow> is_faults_lt_threshold params (\<Union> \<sigma>_set)
  \<Longrightarrow> state_properties_are_consistent params (\<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})" 
  apply simp
  by (smt Collect_mono_iff W.simps equivocation_fault_weight_def is_faults_lt_threshold_def t.simps)


(* Section 3.2.2: Guaranteeing Consistent Decisions on Properties of Consensus Values *)
(* Definition 3.7 *)
type_synonym consensus_value_property = "consensus_value \<Rightarrow> bool"

(* Definition 3.8 *)
definition naturally_corresponding_state_property :: "params \<Rightarrow> consensus_value_property \<Rightarrow> state_property"
  where 
    "naturally_corresponding_state_property params p = (\<lambda>\<sigma>. \<forall>c. c \<in> \<epsilon> params \<sigma> \<and> p c)"

(* Definition 3.9 *)
definition consensus_value_properties_are_consistent :: "params \<Rightarrow> consensus_value_property set \<Rightarrow> bool"
  where
    "consensus_value_properties_are_consistent params p_set = (\<exists> c. c \<in> C params \<and> (\<forall> p. p \<in> p_set \<and> p c))"

(* Lemma 4 *)
lemma naturally_corresponding_consistency :
  "\<forall> params p_set. state_properties_are_consistent params {naturally_corresponding_state_property params p | p. p \<in> p_set}
    \<Longrightarrow> consensus_value_properties_are_consistent params p_set"
  using state_properties_are_consistent_def by auto

(* Definition 3.10 *)
fun consensus_value_property_is_decided :: "params \<Rightarrow> (consensus_value_property * state) \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided params (p, \<sigma>)
      = state_property_is_decided params (naturally_corresponding_state_property params p, \<sigma>)"

(* Definition 3.11 *)
definition consensus_value_property_decisions :: "params \<Rightarrow> state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions params \<sigma> = {p. consensus_value_property_is_decided params (p, \<sigma>)}"

(* Theorem 5 *)
theorem n_party_safety_for_consensus_value_properties :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<Longrightarrow> is_faults_lt_threshold params (\<Union> \<sigma>_set)
  \<Longrightarrow> consensus_value_properties_are_consistent params {p. \<exists> \<sigma>. \<sigma> \<in> \<sigma>_set \<and> p \<in> consensus_value_property_decisions params \<sigma>}"
  apply simp
  using n_party_safety_for_state_properties state_properties_are_consistent_def by force

end
