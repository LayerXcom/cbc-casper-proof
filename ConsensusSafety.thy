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
(* NOTE: Here estimator returns only one value, avoiding non-determinism. 
Also, we parameterized estimator by weight. *)
type_synonym estimator = "weight \<Rightarrow> state \<Rightarrow> consensus_value"


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
    "justification (Message (_, _, ml)) = set ml"

(* Definition 2.7 *)
fun is_valid :: "weight \<Rightarrow>(estimator \<Rightarrow> (message \<Rightarrow> bool))"
  where
    "is_valid w e (Message (c, v, s)) = (c = e w (set s))"

(* FIXME: Can we construct valid_message type? Currently we assume all states are valid in all the 
"definition"s and use is_valid_state for all occurrences of state type in lemmas. *)
definition is_valid_state :: "weight \<Rightarrow> estimator \<Rightarrow> state \<Rightarrow> bool"
  where
    "is_valid_state w e s = (\<forall> m \<in> s. is_valid w e m)"

(* Definition 2.8: Protocol state transitions \<rightarrow> *)
definition is_future_state :: "state \<Rightarrow> state \<Rightarrow> bool"
  where
    "is_future_state s1 s2 = (s1 \<supseteq> s2)"

(* Definition 2.9 *)
definition equivocation :: "message \<Rightarrow> message \<Rightarrow> bool"
  where
    "equivocation m1 m2 =
      (sender m1 = sender m2 \<and> m1 \<noteq> m2 \<and> m1 \<notin> justification(m2) \<and> m2 \<notin> justification(m1))"

(* Definition 2.10 *)
definition equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators s = 
      {v. \<exists> m1 m2. m1 \<in> s \<and> m2 \<in> s \<and> equivocation m1 m2 \<and> sender m1 = v}"

(* Definition 2.11 *)
definition equivocation_fault_weight :: "weight \<Rightarrow> state \<Rightarrow> int"
  where
    "equivocation_fault_weight w s = sum w (equivocating_validators s)"

(* Definition 2.12 *)
definition is_faults_lt_threshold :: "threshold \<Rightarrow> weight \<Rightarrow> state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold t w s = (equivocation_fault_weight w s < t)"

(* Section 3: Safety Proof *)
(* Section 3.1: Guaranteeing Common Futures *)

(* Definition 3.1 *)
definition futures :: "threshold \<Rightarrow> weight \<Rightarrow> state \<Rightarrow> state set"
  where
    "futures t w s = {s'. is_faults_lt_threshold t w s' \<and> is_future_state s' s}"

(* Lemma 1 *)
lemma monotonic_futures :
  "\<forall> s' s. is_faults_lt_threshold t w s' \<and> is_faults_lt_threshold t w s
   \<and> is_valid_state w e s' \<and> is_valid_state w e s
   \<Longrightarrow> (s' \<in> futures t w s \<longleftrightarrow> futures t w s' \<subseteq> futures t w s)"
   using futures_def is_future_state_def by auto

notation Set.empty ("\<emptyset> ")

(* Theorem 1 *)
theorem two_party_common_futures :
  "\<forall> s1 s2. is_faults_lt_threshold t w s1 \<and> is_faults_lt_threshold t w s2
   \<and> is_valid_state w e s1 \<and> is_valid_state w e s2
  \<Longrightarrow> is_faults_lt_threshold t w (s1 \<union> s2)
  \<Longrightarrow> futures t w s1 \<inter> futures t w s2 \<noteq> \<emptyset>"
  using futures_def is_future_state_def by auto

(* Theorem 2 *)
theorem n_party_common_futures :
  "\<forall> s_set. \<forall> s. s \<in> s_set \<and> is_faults_lt_threshold t w s \<and> is_valid_state w e s
  \<Longrightarrow> is_faults_lt_threshold t w (\<Union> s_set)
  \<Longrightarrow> futures t w s1 \<inter> futures t w s2 \<noteq> \<emptyset>"
  by blast

(* Section 3.2: Guaranteeing Consistent Decisions *)
(* Section 3.2.1: Guaranteeing Consistent Decisions on Properties of Protocol States *)

(* Definition 3.2  *)
type_synonym state_property = "state \<Rightarrow> bool"

(* Definition 3.3  *)
definition state_property_is_decided :: "threshold \<Rightarrow> weight \<Rightarrow> state_property \<Rightarrow> state \<Rightarrow> bool"
  where
    "state_property_is_decided t w p s = (\<forall> s'. s' \<in> futures t w s \<and> p s')"

(* Lemma 2 *)
lemma forward_consistency :
  "\<forall> s' s. is_faults_lt_threshold t w s' \<and> is_faults_lt_threshold t w s
   \<and> is_valid_state w e s' \<and> is_valid_state w e s \<and> (\<forall> s'. s' \<in> futures t w s) 
  \<Longrightarrow> state_property_is_decided t w p s
  \<Longrightarrow> state_property_is_decided t w p s'"
  by (simp add: state_property_is_decided_def)

(* Lemma 3 *)
lemma backword_consistency :
  "\<forall> s' s. is_faults_lt_threshold t w s' \<and> is_faults_lt_threshold t w s
   \<and> is_valid_state w e s' \<and> is_valid_state w e s \<and> (\<forall> s'. s' \<in> futures t w s) 
  \<Longrightarrow> state_property_is_decided t w p s'
  \<Longrightarrow> \<not>state_property_is_decided t w (\<lambda>s. (\<not> p s)) s"
  by (simp add: state_property_is_decided_def)
  
(* Theorem 3 *)
theorem two_party_consensus_safety :
  "\<forall> s1 s2. is_faults_lt_threshold t w s1 \<and> is_faults_lt_threshold t w s2
   \<and> is_valid_state w e s1 \<and> is_valid_state w e s2
  \<Longrightarrow> is_faults_lt_threshold t w (s1 \<union> s2)
  \<Longrightarrow> \<not>(state_property_is_decided t w p s1 \<and> state_property_is_decided t w (\<lambda>s. (\<not> p s)) s2)"
  apply (simp add: state_property_is_decided_def)
  by blast  

(* Definition 3.4 *)
(* NOTE: We can use \<And> to make it closer to the paper? *)
definition state_properties_are_inconsistent :: "weight \<Rightarrow> estimator \<Rightarrow> state_property set \<Rightarrow> bool"
  where
    "state_properties_are_inconsistent w e p_set = (\<forall> s. is_valid_state w e s \<and> \<not> (\<forall> p. p \<in> p_set \<and> p s))"

(* Definition 3.5 *)
definition state_properties_are_consistent :: "weight \<Rightarrow> estimator \<Rightarrow> state_property set \<Rightarrow> bool"
  where
    "state_properties_are_consistent w e p_set = (\<exists> s. is_valid_state w e s \<and> (\<forall> p. p \<in> p_set \<and> p s))"

(* Definition 3.6 *)
definition state_property_decisions :: "threshold \<Rightarrow> weight \<Rightarrow> state \<Rightarrow> state_property set"
  where 
    "state_property_decisions t w s = {p. state_property_is_decided t w p s}"

(* Theorem 4 *)
(* NOTE: We can use \<Union> to make it closer to the paper? *)
theorem n_party_safety_for_state_properties :
  "\<forall> s_set. \<forall> s. s \<in> s_set \<and> is_faults_lt_threshold t w s \<and> is_valid_state w e s
  \<Longrightarrow> is_faults_lt_threshold t w (\<Union> s_set)
  \<Longrightarrow> state_properties_are_consistent w e {p. \<exists> s. s \<in> s_set \<and> p \<in> state_property_decisions t w s}" 
  by blast

(* Section 3.2.2: Guaranteeing Consistent Decisions on Properties of Consensus Values *)
(* Definition 3.7 *)
type_synonym consensus_value_property = "consensus_value \<Rightarrow> bool"

(* Definition 3.8 *)
definition naturally_corresponding_state_property :: "weight \<Rightarrow> estimator \<Rightarrow> consensus_value_property \<Rightarrow> state_property"
  where 
    "naturally_corresponding_state_property w e p = (\<lambda>s. \<forall>c. c = e w s \<and> p c)"

(* Definition 3.9 *)
(* NOTE: Here the type of `c` is inferred correctly? *)
definition consensus_value_properties_are_consistent :: "consensus_value_property set \<Rightarrow> bool"
  where
    "consensus_value_properties_are_consistent p_set = (\<exists> c. \<forall> p. p \<in> p_set \<and> p c)"

(* Lemma 4 *)
lemma naturally_corresponding_consistency :
  "\<forall> p_set. state_properties_are_consistent w e {naturally_corresponding_state_property w e p | p. p \<in> p_set}
    \<Longrightarrow> consensus_value_properties_are_consistent p_set"
  using state_properties_are_consistent_def by auto

(* Definition 3.10 *)
definition consensus_value_property_is_decided :: "threshold \<Rightarrow> weight \<Rightarrow> estimator \<Rightarrow> consensus_value_property \<Rightarrow> state \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided t w e p s = state_property_is_decided t w (naturally_corresponding_state_property w e p) s "

(* Definition 3.11 *)
definition consensus_value_property_decisions :: "threshold \<Rightarrow> weight \<Rightarrow> estimator \<Rightarrow> state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions t w e s = {p. consensus_value_property_is_decided t w e p s}"

(* Theorem 5 *)
theorem n_party_safety_for_consensus_value_properties :
  "\<forall> s_set. \<forall> s. s \<in> s_set \<and> is_faults_lt_threshold t w s \<and> is_valid_state w e s
  \<Longrightarrow> is_faults_lt_threshold t w (\<Union> s_set)
  \<Longrightarrow> consensus_value_properties_are_consistent {p. \<exists> s. s \<in> s_set \<and> p \<in> consensus_value_property_decisions t w e s}"
  by blast

end
