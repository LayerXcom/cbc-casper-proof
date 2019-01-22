theory ConsensusSafety

imports Main CBCCasper

begin

(* Section 3: Safety Proof *)
(* Section 3.1: Guaranteeing Common Futures *)

(* Definition 3.1 *)
fun (in Protocol) futures :: "state \<Rightarrow> state set"
  where
    "futures \<sigma> = {\<sigma>' \<in> \<Sigma>t. is_future_state (\<sigma>', \<sigma>)}"

(* Lemma 1 *)
lemma (in Protocol) monotonic_futures :
  "\<forall> \<sigma>' \<sigma>. is_valid_params \<and> \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
   \<longrightarrow> \<sigma>' \<in> futures \<sigma> \<longleftrightarrow> futures \<sigma>' \<subseteq> futures \<sigma>"
  by auto

(* Theorem 1 *)
theorem (in Protocol) two_party_common_futures :
  "\<forall> \<sigma>1 \<sigma>2. is_valid_params \<and> \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t
  \<longrightarrow> futures \<sigma>1 \<inter> futures \<sigma>2 \<noteq> \<emptyset>"
  by auto

(* Theorem 2 *)
theorem (in Protocol) n_party_common_futures :
  "\<forall> \<sigma>_set. is_valid_params \<and> \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t
  \<longrightarrow> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set} \<noteq> \<emptyset>"
  by auto

(* Section 3.2: Guaranteeing Consistent Decisions *)
(* Section 3.2.1: Guaranteeing Consistent Decisions on Properties of Protocol States *)

(* Definition 3.2  *)
type_synonym state_property = "state \<Rightarrow> bool"

fun state_property_not :: "state_property \<Rightarrow> state_property"
  where
    "state_property_not p = (\<lambda>\<sigma>. (\<not> p \<sigma>))"

(* Definition 3.3  *)
fun (in Protocol) state_property_is_decided :: "(state_property * state) \<Rightarrow> bool"
  where
    "state_property_is_decided (p, \<sigma>) = (\<forall> \<sigma>' \<in> futures \<sigma> . p \<sigma>')"

(* Lemma 2 *)
lemma (in Protocol) forward_consistency :
  "\<forall> \<sigma>' \<sigma>. is_valid_params \<and> \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
  \<longrightarrow> \<sigma>' \<in> futures \<sigma> 
  \<longrightarrow> state_property_is_decided (p, \<sigma>)
  \<longrightarrow> state_property_is_decided (p, \<sigma>')"
  apply simp
  by auto

(* Lemma 3 *)
lemma (in Protocol) backword_consistency :
  "\<forall> \<sigma>' \<sigma>. is_valid_params \<and> \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
  \<longrightarrow> \<sigma>' \<in> futures \<sigma> 
  \<longrightarrow> state_property_is_decided (p, \<sigma>')
  \<longrightarrow> \<not>state_property_is_decided (state_property_not p, \<sigma>)"
  apply simp
  by auto
  
(* Theorem 3 *)
theorem (in Protocol) two_party_consensus_safety :
  "\<forall> \<sigma>1 \<sigma>2. is_valid_params \<and> \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t
  \<longrightarrow> \<not>(state_property_is_decided (p, \<sigma>1) \<and> state_property_is_decided (state_property_not p, \<sigma>2))"
  by auto

(* Definition 3.4 *)
fun (in Protocol) state_properties_are_inconsistent :: "state_property set \<Rightarrow> bool"
  where
    "state_properties_are_inconsistent p_set = (\<forall> \<sigma> \<in> \<Sigma> protocol. \<not> (\<forall> p \<in> p_set. p \<sigma>))"

(* Definition 3.5 *)
fun (in Protocol) state_properties_are_consistent :: "state_property set \<Rightarrow> bool"
  where
    "state_properties_are_consistent p_set = (\<exists> \<sigma> \<in> \<Sigma> protocol. \<forall> p \<in> p_set. p \<sigma>)"

(* Definition 3.6 *)
fun (in Protocol) state_property_decisions :: "state \<Rightarrow> state_property set"
  where 
    "state_property_decisions \<sigma> = {p. state_property_is_decided (p, \<sigma>)}"

(* Theorem 4 *)
theorem (in Protocol) n_party_safety_for_state_properties :
  "\<forall> \<sigma>_set. is_valid_params \<and> \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t
  \<longrightarrow> state_properties_are_consistent (\<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})" 
  sorry

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

(* Lemma 4 *)
lemma naturally_corresponding_consistency :
  "\<forall> params q_set. is_valid_params params
  \<longrightarrow> state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> q_set}
  \<longrightarrow> consensus_value_properties_are_consistent params q_set"
  apply (rule, rule, rule)
proof -
  fix params q_set
  assume hyp: "is_valid_params params"

  have 
    "state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> q_set}
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)"
    by simp
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q' \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q' c) \<sigma>)"
    by (metis (mono_tags, lifting) mem_Collect_eq)
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c) \<sigma>)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q' \<in> q_set. \<forall> c \<in> \<epsilon> params \<sigma>. q' c)"
    by blast
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q \<in> q_set. \<forall> c \<in> \<epsilon> params \<sigma>. q c)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> c \<in> \<epsilon> params \<sigma>. \<forall> q' \<in> q_set. q' c)"
    by blast
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma> params. \<forall> c \<in> \<epsilon> params \<sigma>. \<forall> q \<in> q_set. q c)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<exists> c \<in> \<epsilon> params \<sigma>. \<forall> q' \<in> q_set. q' c)"
    using hyp
    by (meson equals0I estimates_are_non_empty)
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma> params. \<exists> c \<in> \<epsilon> params \<sigma>. \<forall> q \<in> q_set. q c)
    \<longrightarrow> (\<exists> c \<in> C params. \<forall> q' \<in> q_set. q' c)"
    using estimate_is_valid hyp by auto  
  ultimately show
    "state_properties_are_consistent params {naturally_corresponding_state_property params q |q. q \<in> q_set}
    \<longrightarrow> consensus_value_properties_are_consistent params q_set"
    by simp
qed

(* Definition 3.10 *)
fun consensus_value_property_is_decided :: "params \<Rightarrow> (consensus_value_property * state) \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided params (q, \<sigma>)
      = state_property_is_decided params (naturally_corresponding_state_property params q, \<sigma>)"

(* Definition 3.11 *)
fun consensus_value_property_decisions :: "params \<Rightarrow> state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions params \<sigma> = {q. consensus_value_property_is_decided params (q, \<sigma>)}"

(* Theorem 5 *)
theorem n_party_safety_for_consensus_value_properties :
  "\<forall> params \<sigma>_set. is_valid_params params \<and> \<sigma>_set \<subseteq> \<Sigma>t params
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t params
  \<longrightarrow> consensus_value_properties_are_consistent params (\<Union> {consensus_value_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
  apply (rule, rule, rule)
proof -
  fix params \<sigma>_set
  assume hyp: "is_valid_params params \<and> \<sigma>_set \<subseteq> \<Sigma>t params"

  have
    "\<Union> \<sigma>_set \<in> \<Sigma>t params
    \<longrightarrow> state_properties_are_consistent params (\<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    by auto
  moreover have
    "state_properties_are_consistent params (\<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})
    \<longrightarrow> state_properties_are_consistent params {p. \<exists> q. p \<in> (\<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}) \<and> p = naturally_corresponding_state_property params q}"
    by (smt mem_Collect_eq state_properties_are_consistent.simps)
  moreover have
    "state_properties_are_consistent params {p. \<exists> q. p \<in> (\<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}) \<and> p = naturally_corresponding_state_property params q}
    \<longrightarrow> state_properties_are_consistent params {naturally_corresponding_state_property params q | q. naturally_corresponding_state_property params q \<in> \<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}}"
    by (smt Collect_cong)
  moreover have
    "state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> {q. naturally_corresponding_state_property params q \<in> \<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}}}
    \<longrightarrow> consensus_value_properties_are_consistent params {q. naturally_corresponding_state_property params q \<in> \<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}}"
    using naturally_corresponding_consistency hyp
    by blast
  moreover have
    "consensus_value_properties_are_consistent params {q. naturally_corresponding_state_property params q \<in> \<Union> {state_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}}
    \<longrightarrow> consensus_value_properties_are_consistent params (\<Union> {consensus_value_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    apply simp
    by (smt mem_Collect_eq)
  ultimately show
    "\<Union> \<sigma>_set \<in> \<Sigma>t params
    \<longrightarrow> consensus_value_properties_are_consistent params (\<Union> {consensus_value_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    by simp
qed

end
