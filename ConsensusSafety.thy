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
  "\<forall> \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
   \<longrightarrow> \<sigma>' \<in> futures \<sigma> \<longleftrightarrow> futures \<sigma>' \<subseteq> futures \<sigma>"
  by auto

(* Theorem 1 *)
theorem (in Protocol) two_party_common_futures :
  "\<forall> \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t
  \<longrightarrow> futures \<sigma>1 \<inter> futures \<sigma>2 \<noteq> \<emptyset>"
  by auto

(* Theorem 2 *)
theorem (in Protocol) n_party_common_futures :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
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
  "\<forall> \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
  \<longrightarrow> \<sigma>' \<in> futures \<sigma> 
  \<longrightarrow> state_property_is_decided (p, \<sigma>)
  \<longrightarrow> state_property_is_decided (p, \<sigma>')"
  apply simp
  by auto

(* Lemma 3 *)
lemma (in Protocol) backword_consistency :
  "\<forall> \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
  \<longrightarrow> \<sigma>' \<in> futures \<sigma> 
  \<longrightarrow> state_property_is_decided (p, \<sigma>')
  \<longrightarrow> \<not>state_property_is_decided (state_property_not p, \<sigma>)"
  apply simp
  by auto
  
(* Theorem 3 *)
theorem (in Protocol) two_party_consensus_safety :
  "\<forall> \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>1 \<union> \<sigma>2) \<in> \<Sigma>t
  \<longrightarrow> \<not>(state_property_is_decided (p, \<sigma>1) \<and> state_property_is_decided (state_property_not p, \<sigma>2))"
  by auto

(* Definition 3.4 *)
fun (in Protocol) state_properties_are_inconsistent :: "state_property set \<Rightarrow> bool"
  where
    "state_properties_are_inconsistent p_set = (\<forall> \<sigma> \<in> \<Sigma>. \<not> (\<forall> p \<in> p_set. p \<sigma>))"

(* Definition 3.5 *)
fun (in Protocol) state_properties_are_consistent :: "state_property set \<Rightarrow> bool"
  where
    "state_properties_are_consistent p_set = (\<exists> \<sigma> \<in> \<Sigma>. \<forall> p \<in> p_set. p \<sigma>)"

(* Definition 3.6 *)
fun (in Protocol) state_property_decisions :: "state \<Rightarrow> state_property set"
  where 
    "state_property_decisions \<sigma> = {p. state_property_is_decided (p, \<sigma>)}"

(* Theorem 4 *)
theorem (in Protocol) n_party_safety_for_state_properties :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t
  \<longrightarrow> state_properties_are_consistent (\<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
  apply rule+
proof-
  fix \<sigma>_set
  assume \<sigma>_set: "\<sigma>_set \<subseteq> \<Sigma>t"

  assume "\<Union> \<sigma>_set \<in> \<Sigma>t"
  hence "\<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set} \<noteq> \<emptyset>"
    using \<sigma>_set by auto
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<sigma> \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}"
    using \<open>\<Union>\<sigma>_set \<in> \<Sigma>t\<close> by fastforce
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. \<sigma> \<in> futures s"
    by blast
  hence "\<exists>\<sigma>\<in>\<Sigma>t. (\<forall>s\<in>\<sigma>_set. \<sigma> \<in> futures s) \<and> (\<forall>s\<in>\<sigma>_set. \<sigma> \<in> futures s \<longrightarrow> (\<forall>p. state_property_is_decided (p,s) \<longrightarrow> state_property_is_decided (p,\<sigma>)))"
    by (simp add: subset_eq)
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. (\<forall>p. state_property_is_decided (p,s) \<longrightarrow> state_property_is_decided (p,\<sigma>))"
    by blast
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. (\<forall>p \<in> state_property_decisions s. state_property_is_decided (p,\<sigma>))"
    by simp
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>p\<in>\<Union>{state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}. state_property_is_decided (p,\<sigma>)"
  proof-
    obtain \<sigma> where "\<sigma> \<in> \<Sigma>t" "\<forall>s\<in>\<sigma>_set. (\<forall>p \<in> state_property_decisions s. state_property_is_decided (p,\<sigma>))"
      using \<open>\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. \<forall>p\<in>state_property_decisions s. state_property_is_decided (p, \<sigma>)\<close> by blast
    have "\<forall>p\<in>\<Union>{state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}. state_property_is_decided (p,\<sigma>)"
      using \<open>\<forall>s\<in>\<sigma>_set. \<forall>p\<in>state_property_decisions s. state_property_is_decided (p, \<sigma>)\<close> by fastforce
    thus ?thesis
      using \<open>\<sigma> \<in> \<Sigma>t\<close> by blast
  qed
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>p\<in>\<Union>{state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}. \<forall>\<sigma>'\<in>futures \<sigma>. p \<sigma>'"
    by simp
  show "state_properties_are_consistent (\<Union>{state_property_decisions \<sigma> |\<sigma>. \<sigma> \<in> \<sigma>_set})"
    by (metis (mono_tags, lifting) \<Sigma>t_def \<open>\<exists>\<sigma>\<in>\<Sigma>t. \<forall>p\<in>\<Union>{state_property_decisions \<sigma> |\<sigma>. \<sigma> \<in> \<sigma>_set}. \<forall>\<sigma>'\<in>futures \<sigma>. p \<sigma>'\<close> mem_Collect_eq monotonic_futures order_refl state_properties_are_consistent.simps)
qed

(* Section 3.2.2: Guaranteeing Consistent Decisions on Properties of Consensus Values *)
(* Definition 3.7 *)
type_synonym consensus_value_property = "consensus_value \<Rightarrow> bool"

(* Definition 3.8 *)
fun (in Protocol) naturally_corresponding_state_property :: "consensus_value_property \<Rightarrow> state_property"
  where 
    "naturally_corresponding_state_property q = (\<lambda>\<sigma>. \<forall> c \<in> \<epsilon> \<sigma>. q c)"

(* Definition 3.9 *)
fun (in Protocol) consensus_value_properties_are_consistent :: "consensus_value_property set \<Rightarrow> bool"
  where
    "consensus_value_properties_are_consistent q_set = (\<exists> c \<in> C. \<forall> q \<in> q_set. q c)"

(* Lemma 4 *)
lemma (in Protocol) naturally_corresponding_consistency :
  "\<forall> q_set. state_properties_are_consistent {naturally_corresponding_state_property q | q. q \<in> q_set}
  \<longrightarrow> consensus_value_properties_are_consistent q_set"
  apply (rule, rule)
proof -
  fix q_set

  have 
    "state_properties_are_consistent {naturally_corresponding_state_property q | q. q \<in> q_set}
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma>. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)"
    by simp
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma>. \<forall> p \<in> {\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> \<sigma>'. q c | q. q \<in> q_set}. p \<sigma>)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma>. \<forall> q' \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> \<sigma>'. q' c) \<sigma>)"
    by (metis (mono_tags, lifting) mem_Collect_eq)
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma>. \<forall> q \<in> q_set. (\<lambda>\<sigma>'. \<forall> c \<in> \<epsilon> \<sigma>'. q c) \<sigma>)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma>. \<forall> q' \<in> q_set. \<forall> c \<in> \<epsilon> \<sigma>. q' c)"
    by blast
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma>. \<forall> q \<in> q_set. \<forall> c \<in> \<epsilon> \<sigma>. q c)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma>. \<forall> c \<in> \<epsilon> \<sigma>. \<forall> q' \<in> q_set. q' c)"
    by blast
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma>. \<forall> c \<in> \<epsilon> \<sigma>. \<forall> q \<in> q_set. q c)
    \<longrightarrow> (\<exists> \<sigma> \<in> \<Sigma>. \<exists> c \<in> \<epsilon> \<sigma>. \<forall> q' \<in> q_set. q' c)"
    by (meson all_not_in_conv estimates_are_non_empty)
  moreover have
    "(\<exists> \<sigma> \<in> \<Sigma>. \<exists> c \<in> \<epsilon> \<sigma>. \<forall> q \<in> q_set. q c)
    \<longrightarrow> (\<exists> c \<in> C. \<forall> q' \<in> q_set. q' c)"
    using \<epsilon>_type by fastforce
  ultimately show
    "state_properties_are_consistent {naturally_corresponding_state_property q |q. q \<in> q_set}
    \<Longrightarrow> consensus_value_properties_are_consistent q_set"
    by simp
qed

(* Definition 3.10 *)
fun (in Protocol) consensus_value_property_is_decided :: "(consensus_value_property * state) \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided (q, \<sigma>)
      = state_property_is_decided (naturally_corresponding_state_property q, \<sigma>)"

(* Definition 3.11 *)
fun (in Protocol) consensus_value_property_decisions :: "state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions \<sigma> = {q. consensus_value_property_is_decided (q, \<sigma>)}"

(* Theorem 5 *)
theorem (in Protocol) n_party_safety_for_consensus_value_properties :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> \<Union> \<sigma>_set \<in> \<Sigma>t
  \<longrightarrow> consensus_value_properties_are_consistent (\<Union> {consensus_value_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
  apply (rule, rule, rule)
proof -
  fix \<sigma>_set
  assume "\<sigma>_set \<subseteq> \<Sigma>t"

  assume "\<Union> \<sigma>_set \<in> \<Sigma>t"
  hence "state_properties_are_consistent (\<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    using \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> n_party_safety_for_state_properties by auto
  hence "state_properties_are_consistent {p \<in> \<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}. \<exists> q. p = naturally_corresponding_state_property q}"
    apply simp
    by meson 
  hence "state_properties_are_consistent {naturally_corresponding_state_property q | q. naturally_corresponding_state_property q \<in> \<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}}"
    by (smt Collect_cong)
  hence "consensus_value_properties_are_consistent {q. naturally_corresponding_state_property q \<in> \<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}}"
    using naturally_corresponding_consistency
  proof -
    show ?thesis
      by (metis (no_types) Setcompr_eq_image \<open>\<forall>q_set. state_properties_are_consistent {naturally_corresponding_state_property q |q. q \<in> q_set} \<longrightarrow> consensus_value_properties_are_consistent q_set\<close> \<open>state_properties_are_consistent {naturally_corresponding_state_property q |q. naturally_corresponding_state_property q \<in> \<Union>{state_property_decisions \<sigma> |\<sigma>. \<sigma> \<in> \<sigma>_set}}\<close> setcompr_eq_image)
  qed
  hence "consensus_value_properties_are_consistent (\<Union> {consensus_value_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    apply simp
    by (smt mem_Collect_eq)
  thus
    "consensus_value_properties_are_consistent (\<Union> {consensus_value_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    by simp
qed

end
