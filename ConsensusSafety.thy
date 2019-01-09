theory ConsensusSafety

imports Main CBCCasper

begin

(* Section 3: Safety Proof *)
(* Section 3.1: Guaranteeing Common Futures *)

(* Definition 3.1 *)
fun futures :: "params \<Rightarrow> state \<Rightarrow> state set"
  where
    "futures params \<sigma> = {\<sigma>'. is_faults_lt_threshold params \<sigma>' \<and> is_future_state (\<sigma>', \<sigma>)}"

(* Lemma 1 *)
lemma monotonic_futures :
  "\<forall> params \<sigma>' \<sigma>. is_valid_params params \<and> \<sigma>' \<in> \<Sigma>t params \<and> \<sigma> \<in> \<Sigma>t params
   \<longrightarrow> \<sigma>' \<in> futures params \<sigma> \<longleftrightarrow> futures params \<sigma>' \<subseteq> futures params \<sigma>"
  by fastforce

(* Theorem 1 *)
theorem two_party_common_futures :
  "\<forall> params \<sigma>1 \<sigma>2. is_valid_params params \<and> \<sigma>1 \<in> \<Sigma>t params \<and> \<sigma>2 \<in> \<Sigma>t params
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t params
  \<longrightarrow> futures params \<sigma>1 \<inter> futures params \<sigma>2 \<noteq> \<emptyset>"
  by auto

(* Theorem 2 *)
theorem n_party_common_futures :
  "\<forall> params \<sigma>_set. is_valid_params params \<and> \<sigma>_set \<subseteq> \<Sigma>t params
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
  "\<forall> params \<sigma>' \<sigma>. is_valid_params params \<and> \<sigma>' \<in> \<Sigma>t params \<and> \<sigma> \<in> \<Sigma>t params
  \<longrightarrow> \<sigma>' \<in> futures params \<sigma> 
  \<longrightarrow> state_property_is_decided params (p, \<sigma>)
  \<longrightarrow> state_property_is_decided params (p, \<sigma>')"
  apply simp
  by auto

(* Lemma 3 *)
lemma backword_consistency :
  "\<forall> params \<sigma>' \<sigma>. is_valid_params params \<and> \<sigma>' \<in> \<Sigma>t params \<and> \<sigma> \<in> \<Sigma>t params
  \<longrightarrow> \<sigma>' \<in> futures params \<sigma> 
  \<longrightarrow> state_property_is_decided params (p, \<sigma>')
  \<longrightarrow> \<not>state_property_is_decided params (state_property_not p, \<sigma>)"
  apply simp
  by auto
  
(* Theorem 3 *)
theorem two_party_consensus_safety :
  "\<forall> params \<sigma>1 \<sigma>2. is_valid_params params \<and> \<sigma>1 \<in> \<Sigma>t params \<and> \<sigma>2 \<in> \<Sigma>t params
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
  "\<forall> params \<sigma>_set. is_valid_params params \<and> \<sigma>_set \<subseteq> \<Sigma>t params
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

(* Lemma 4 *)
lemma proof_line_86 :
  "\<forall> params q_set. is_valid_params params
    \<longrightarrow> state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> q_set}
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)"
  by simp

lemma proof_line_87 :
  "\<forall> params q_set. is_valid_params params
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q' \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q' c) \<sigma>)"
  by fastforce  

lemma proof_line_88 :
  "\<forall> params q_set. is_valid_params params
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> params \<sigma>'. q c) \<sigma>)
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q' \<in> q_set. \<forall> c \<in> \<epsilon> params \<sigma>. q' c)"
  by blast

lemma proof_line_89 :
  "\<forall> params q_set. is_valid_params params
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> q \<in> q_set. \<forall> c \<in> \<epsilon> params \<sigma>. q c)
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> c \<in> \<epsilon> params \<sigma>. \<forall> q' \<in> q_set. q' c)"
  by blast

lemma proof_line_90 :
  "\<forall> params q_set. is_valid_params params 
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<forall> c \<in> \<epsilon> params \<sigma>. \<forall> q \<in> q_set. q c)
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<exists> c \<in> \<epsilon> params \<sigma>. \<forall> q' \<in> q_set. q' c)"
  by (meson is_non_empty_def is_valid_estimator_def is_valid_params_def)

lemma proof_line_91 :
  "\<forall> params q_set. is_valid_params params 
  \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma> params. \<exists> c \<in> \<epsilon> params \<sigma>. \<forall> q \<in> q_set. q c)
  \<longrightarrow> (\<exists> c \<in> C params. \<forall> q' \<in> q_set. q' c)"
  using estimates_are_valid by auto

lemma naturally_corresponding_consistency :
  "\<forall> params q_set. is_valid_params params
  \<longrightarrow> state_properties_are_consistent params {naturally_corresponding_state_property params q | q. q \<in> q_set}
  \<longrightarrow> consensus_value_properties_are_consistent params q_set"
  using proof_line_87 proof_line_89 proof_line_90 proof_line_91 by auto  

(* Definition 3.10 *)
fun consensus_value_property_is_decided :: "params \<Rightarrow> (consensus_value_property * state) \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided params (q, \<sigma>)
      = state_property_is_decided params (naturally_corresponding_state_property params q, \<sigma>)"

(* Definition 3.11 *)
definition consensus_value_property_decisions :: "params \<Rightarrow> state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions params \<sigma> = {q. consensus_value_property_is_decided params (q, \<sigma>)}"
(* 
(* Theorem 5 *)
theorem n_party_safety_for_consensus_value_properties :
  "\<forall> params \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t params
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t params
  \<longrightarrow> consensus_value_properties_are_consistent params (\<Union> {consensus_value_property_decisions params \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
 *)

end
