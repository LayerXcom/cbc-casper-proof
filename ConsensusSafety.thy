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
type_synonym estimator_param = "weight \<Rightarrow> estimator"

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

(* NOTE: Enforce estimator to return valid consensus values *)
fun \<epsilon> :: "params \<Rightarrow> estimator"
  where
    "\<epsilon> (Params (_, weight, _, c_set, estimator_param)) = (\<lambda> \<sigma>. estimator_param weight \<sigma>  \<inter> c_set)"


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
  "\<forall> params \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t params \<and> \<sigma> \<in> \<Sigma>t params
   \<longrightarrow> \<sigma>' \<in> futures params \<sigma> \<longleftrightarrow> futures params \<sigma>' \<subseteq> futures params \<sigma>"
  by fastforce

notation Set.empty ("\<emptyset>")

(* Theorem 1 *)
theorem two_party_common_futures :
  "\<forall> params \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t params \<and> \<sigma>2 \<in> \<Sigma>t params
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t params
  \<longrightarrow> futures params \<sigma>1 \<inter> futures params \<sigma>2 \<noteq> \<emptyset>"
  by auto

(* Theorem 2 *)
theorem n_party_common_futures :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t params
  \<longrightarrow> \<Inter> {futures params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set} \<noteq> \<emptyset>"
  by auto

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
    "state_property_is_decided params (p, \<sigma>) = (\<forall> \<sigma>' \<in> futures params \<sigma> . p \<sigma>')"

(* Lemma 2 *)
lemma forward_consistency :
  "\<forall> params \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t params \<and> \<sigma> \<in> \<Sigma>t params
  \<longrightarrow> \<sigma>' \<in> futures params \<sigma> 
  \<longrightarrow> state_property_is_decided params (p, \<sigma>)
  \<longrightarrow> state_property_is_decided params (p, \<sigma>')"
  apply simp
  by auto

(* Lemma 3 *)
lemma backword_consistency :
  "\<forall> params \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t params \<and> \<sigma> \<in> \<Sigma>t params
  \<longrightarrow> \<sigma>' \<in> futures params \<sigma> 
  \<longrightarrow> state_property_is_decided params (p, \<sigma>')
  \<longrightarrow> \<not>state_property_is_decided params (state_property_not p, \<sigma>)"
  apply simp
  by auto
  
(* Theorem 3 *)
theorem two_party_consensus_safety :
  "\<forall> params \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t params \<and> \<sigma>2 \<in> \<Sigma>t params
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t params
  \<longrightarrow> \<not>(state_property_is_decided params (p, \<sigma>1) \<and> state_property_is_decided params (state_property_not p, \<sigma>2))"
  by auto

(* Definition 3.4 *)
fun state_properties_are_inconsistent :: "params \<Rightarrow> state_property set \<Rightarrow> bool"
  where
    "state_properties_are_inconsistent params p_set = (\<forall> \<sigma> \<in> \<Sigma> params. \<not> (\<forall> p \<in> p_set. p \<sigma>))"

(* Definition 3.5 *)
fun state_properties_are_consistent :: "params \<Rightarrow> state_property set \<Rightarrow> bool"
  where
    "state_properties_are_consistent params p_set = (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> p_set. p \<sigma>)"

(* Definition 3.6 *)
fun state_property_decisions :: "params \<Rightarrow> state \<Rightarrow> state_property set"
  where 
    "state_property_decisions params \<sigma> = {p. state_property_is_decided params (p, \<sigma>)}"

(* Theorem 4 *)
theorem n_party_safety_for_state_properties :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t params
  \<longrightarrow> state_properties_are_consistent params (\<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})" 
  by auto 

(* Section 3.2.2: Guaranteeing Consistent Decisions on Properties of Consensus Values *)
(* Definition 3.7 *)
type_synonym consensus_value_property = "consensus_value \<Rightarrow> bool"

(* Definition 3.8 *)
fun naturally_corresponding_state_property :: "params \<Rightarrow> consensus_value_property \<Rightarrow> state_property"
  where 
    "naturally_corresponding_state_property params q = (\<lambda>\<sigma>. \<forall> c \<in> \<epsilon> params \<sigma>. q c)"

(* Definition 3.9 *)
fun consensus_value_properties_are_consistent :: "params \<Rightarrow> consensus_value_property set \<Rightarrow> bool"
  where
    "consensus_value_properties_are_consistent params q_set = (\<exists> c \<in> C params. \<forall> q \<in> q_set. q c)"


lemma estimates_are_valid:
  "\<forall> params c. c \<in> \<epsilon> params \<sigma> \<longrightarrow> c \<in> C params"
  by (metis C.simps IntE \<epsilon>.elims)  

lemma extend_state_properties_are_consistent_def :
  "\<forall> params q_set. state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> q_set}
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)"
  apply simp
  done

(*  
lemma extract_without_lambda :
  "\<forall> params p_set. (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. p \<sigma>' | p. p \<in> p_set}. p \<sigma>) \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> p_set. p \<sigma>)"
  by simp

lemma extract_lambda :
  "\<forall> params p_set. (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. p \<sigma>' | p. p \<in> p_set}. p \<sigma>) \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> p_set. (\<lambda>\<sigma>'. p \<sigma>') \<sigma>)"
  by simp

lemma extract_lambda_with_exists :
  "\<forall> params q_set. (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<exists> c \<in> \<epsilon> params \<sigma>'. q \<sigma>' | q. q \<in> q_set}. p \<sigma>) \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q \<in> q_set. (\<lambda>\<sigma>'. \<exists> c \<in> \<epsilon> params \<sigma>'. q \<sigma>') \<sigma>)"
  apply simp


lemma extract_lambda_with_forall :
  "\<forall> params q_set. (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>) \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c) \<sigma>)"
  apply simp  

lemma tmp1 :
  "\<forall> params q_set. \<exists> \<sigma> \<in> \<Sigma> params. 
    (\<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>
    \<longrightarrow> (\<forall> c \<in> \<epsilon> params \<sigma>. \<forall> q \<in> q_set. q c))"
  apply simp

lemma tmp2 :
  "\<forall> params q_set. \<exists> \<sigma> \<in> \<Sigma> params. 
    (\<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>
    \<longrightarrow> (\<exists> c \<in> \<epsilon> params \<sigma>. \<forall> q \<in> q_set. q c))"
  apply simp

 *)
lemma naturally_corresponding_consistency :
  "\<forall> params q_set. state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> q_set}
    \<longrightarrow> consensus_value_properties_are_consistent params q_set"
  apply auto


(* Definition 3.10 *)
fun consensus_value_property_is_decided :: "params \<Rightarrow> (consensus_value_property * state) \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided params (q, \<sigma>)
      = state_property_is_decided params (naturally_corresponding_state_property params q, \<sigma>)"

(* Definition 3.11 *)
definition consensus_value_property_decisions :: "params \<Rightarrow> state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions params \<sigma> = {q. consensus_value_property_is_decided params (q, \<sigma>)}"

(* Theorem 5 *)
theorem n_party_safety_for_consensus_value_properties :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t params
  \<longrightarrow> consensus_value_properties_are_consistent params (\<Union> {consensus_value_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"

end
