section \<open>Safety Proof\<close>

theory ConsensusSafety

imports Main CBCCasper MessageJustification StateTransition "Libraries/LaTeXsugar"

begin

(* Section 3: Safety Proof *)
(* Section 3.1: Guaranteeing Common Futures *)

(* Definition 3.1 *)
definition (in Protocol) futures :: "state \<Rightarrow> state set"
  where
    "futures \<sigma> = {\<sigma>' \<in> \<Sigma>t. is_future_state (\<sigma>, \<sigma>')}"

(* Lemma 1 *)
lemma (in Protocol) monotonic_futures :
  "\<forall> \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
   \<longrightarrow> \<sigma>' \<in> futures \<sigma> \<longleftrightarrow> futures \<sigma>' \<subseteq> futures \<sigma>"
  apply (simp add: futures_def) by auto

(* Theorem 1 *)
theorem (in Protocol) two_party_common_futures :
  "\<forall> \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)
  \<longrightarrow> futures \<sigma>1 \<inter> futures \<sigma>2 \<noteq> \<emptyset>"
  apply (simp add: futures_def \<Sigma>t_def) using union_of_two_states_is_state
  by blast

(* Theorem 2 *)
theorem (in Protocol) n_party_common_futures :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set} \<noteq> \<emptyset>"
  apply (simp add: futures_def \<Sigma>t_def) using union_of_finite_set_of_states_is_state
  by blast

lemma (in Protocol) n_party_common_futures_exists :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> (\<exists> \<sigma> \<in>\<Sigma>t. \<sigma> \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
  apply (simp add: futures_def \<Sigma>t_def) using union_of_finite_set_of_states_is_state
  by blast

(* Section 3.2: Guaranteeing Consistent Decisions *)
(* Section 3.2.1: Guaranteeing Consistent Decisions on Properties of Protocol States *)

(* Definition 3.3  *)
definition (in Protocol) state_property_is_decided :: "(state_property * state) \<Rightarrow> bool"
  where
    "state_property_is_decided = (\<lambda>(p, \<sigma>). (\<forall> \<sigma>' \<in> futures \<sigma> . p \<sigma>'))"

(* Lemma 2 *)
lemma (in Protocol) forward_consistency :
  "\<forall> \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
  \<longrightarrow> \<sigma>' \<in> futures \<sigma> 
  \<longrightarrow> state_property_is_decided (p, \<sigma>)
  \<longrightarrow> state_property_is_decided (p, \<sigma>')"
  apply (simp add: futures_def state_property_is_decided_def)
  by auto

(* Lemma 3 *)
fun state_property_not :: "state_property \<Rightarrow> state_property"
  where
    "state_property_not p = (\<lambda>\<sigma>. (\<not> p \<sigma>))"

lemma (in Protocol) backword_consistency :
  "\<forall> \<sigma>' \<sigma>. \<sigma>' \<in> \<Sigma>t \<and> \<sigma> \<in> \<Sigma>t
  \<longrightarrow> \<sigma>' \<in> futures \<sigma> 
  \<longrightarrow> state_property_is_decided (p, \<sigma>')
  \<longrightarrow> \<not>state_property_is_decided (state_property_not p, \<sigma>)"
  apply (simp add: futures_def state_property_is_decided_def)
  by auto
  
(* Theorem 3 *)
theorem (in Protocol) two_party_consensus_safety_for_state_property :
  "\<forall> \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)
  \<longrightarrow> \<not>(state_property_is_decided (p, \<sigma>1) \<and> state_property_is_decided (state_property_not p, \<sigma>2))"
  apply (simp add: state_property_is_decided_def)
  using two_party_common_futures
  by (metis Int_emptyI)

(* Definition 3.4 *)
definition (in Protocol) state_properties_are_inconsistent :: "state_property set \<Rightarrow> bool"
  where
    "state_properties_are_inconsistent p_set = (\<forall> \<sigma> \<in> \<Sigma>. \<not> (\<forall> p \<in> p_set. p \<sigma>))"

(* Definition 3.5 *)
definition (in Protocol) state_properties_are_consistent :: "state_property set \<Rightarrow> bool"
  where
    "state_properties_are_consistent p_set = (\<exists> \<sigma> \<in> \<Sigma>. \<forall> p \<in> p_set. p \<sigma>)"

(* Definition 3.6 *)
definition (in Protocol) state_property_decisions :: "state \<Rightarrow> state_property set"
  where 
    "state_property_decisions \<sigma> = {p. state_property_is_decided (p, \<sigma>)}"

(* Theorem 4 *)
theorem (in Protocol) n_party_safety_for_state_properties :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> state_properties_are_consistent (\<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
  apply rule+
proof-
  fix \<sigma>_set
  assume \<sigma>_set: "\<sigma>_set \<subseteq> \<Sigma>t"
  and "finite \<sigma>_set"
  and "is_faults_lt_threshold (\<Union> \<sigma>_set)"
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<sigma> \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}"
    using n_party_common_futures_exists by simp
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. \<sigma> \<in> futures s"
    by blast
  hence "\<exists>\<sigma>\<in>\<Sigma>t. (\<forall>s\<in>\<sigma>_set. \<sigma> \<in> futures s) \<and> (\<forall>s\<in>\<sigma>_set. \<sigma> \<in> futures s \<longrightarrow> (\<forall>p. state_property_is_decided (p,s) \<longrightarrow> state_property_is_decided (p,\<sigma>)))"
    by (simp add: subset_eq state_property_is_decided_def futures_def)
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. (\<forall>p. state_property_is_decided (p,s) \<longrightarrow> state_property_is_decided (p,\<sigma>))"
    by blast
  hence "\<exists>\<sigma>\<in>\<Sigma>t. \<forall>s\<in>\<sigma>_set. (\<forall>p \<in> state_property_decisions s. state_property_is_decided (p,\<sigma>))"
    by (simp add: state_property_decisions_def)
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
    by (simp add: state_property_decisions_def futures_def state_property_is_decided_def)
  show "state_properties_are_consistent (\<Union>{state_property_decisions \<sigma> |\<sigma>. \<sigma> \<in> \<sigma>_set})"
    unfolding state_properties_are_consistent_def 
    by (metis (mono_tags, lifting) \<Sigma>t_def \<open>\<exists>\<sigma>\<in>\<Sigma>t. \<forall>p\<in>\<Union>{state_property_decisions \<sigma> |\<sigma>. \<sigma> \<in> \<sigma>_set}. \<forall>\<sigma>'\<in>futures \<sigma>. p \<sigma>'\<close> mem_Collect_eq monotonic_futures order_refl)
qed

(* Section 3.2.2: Guaranteeing Consistent Decisions on Properties of Consensus Values *)

(* Definition 3.8 *)
definition (in Protocol) naturally_corresponding_state_property :: "consensus_value_property \<Rightarrow> state_property"
  where 
    "naturally_corresponding_state_property q = (\<lambda>\<sigma>. \<forall> c \<in> \<epsilon> \<sigma>. q c)"

(* Definition 3.9 *)
definition (in Protocol) consensus_value_properties_are_consistent :: "consensus_value_property set \<Rightarrow> bool"
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
    by (simp add: naturally_corresponding_state_property_def state_properties_are_consistent_def)
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
    using is_valid_estimator_def \<epsilon>_type by fastforce
  ultimately show
    "state_properties_are_consistent {naturally_corresponding_state_property q |q. q \<in> q_set}
    \<Longrightarrow> consensus_value_properties_are_consistent q_set"
    by (simp add: consensus_value_properties_are_consistent_def)
qed

(* Definition 3.10 *)
definition (in Protocol) consensus_value_property_is_decided :: "(consensus_value_property * state) \<Rightarrow> bool"
  where
    "consensus_value_property_is_decided 
      = (\<lambda>(q, \<sigma>). state_property_is_decided (naturally_corresponding_state_property q, \<sigma>))"

(* Definition 3.11 *)
definition (in Protocol) consensus_value_property_decisions :: "state \<Rightarrow> consensus_value_property set"
  where
    "consensus_value_property_decisions \<sigma> = {q. consensus_value_property_is_decided (q, \<sigma>)}"

(* Theorem 5 *)
theorem (in Protocol) n_party_safety_for_consensus_value_properties :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> consensus_value_properties_are_consistent (\<Union> {consensus_value_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
  apply (rule, rule, rule, rule)
proof -
  fix \<sigma>_set
  assume "\<sigma>_set \<subseteq> \<Sigma>t"
  and "finite \<sigma>_set"
  and "is_faults_lt_threshold (\<Union> \<sigma>_set)"
  hence "state_properties_are_consistent (\<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    using \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> n_party_safety_for_state_properties by auto
  hence "state_properties_are_consistent {p \<in> \<Union> {state_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}. \<exists> q. p = naturally_corresponding_state_property q}"
    unfolding naturally_corresponding_state_property_def state_properties_are_consistent_def
    apply (simp)
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
    apply (simp add: consensus_value_property_decisions_def consensus_value_property_is_decided_def state_property_decisions_def consensus_value_properties_are_consistent_def)
    by (metis mem_Collect_eq)
  thus
    "consensus_value_properties_are_consistent (\<Union> {consensus_value_property_decisions \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set})"
    by simp
qed

fun consensus_value_property_not :: "consensus_value_property \<Rightarrow> consensus_value_property"
  where
    "consensus_value_property_not p = (\<lambda>c. (\<not> p c))"

lemma (in Protocol) negation_is_not_decided_by_other_validator :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> (\<forall> \<sigma> \<sigma>' p. {\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> p \<in> consensus_value_property_decisions \<sigma> 
            \<longrightarrow> consensus_value_property_not p \<notin> consensus_value_property_decisions \<sigma>')"
  apply (rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma>_set \<sigma> \<sigma>' p
  assume "\<sigma>_set \<subseteq> \<Sigma>t" and "finite \<sigma>_set" and "is_faults_lt_threshold (\<Union>\<sigma>_set)" and "{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> p \<in> consensus_value_property_decisions \<sigma>" 
  hence "\<exists> \<sigma>. \<sigma> \<in> \<Sigma>t \<and> \<sigma> \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}"
    using n_party_common_futures_exists by meson
  then obtain \<sigma>'' where "\<sigma>'' \<in> \<Sigma>t \<and> \<sigma>'' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}" by auto
  hence "state_property_is_decided (naturally_corresponding_state_property p, \<sigma>'')" 
    using \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> p \<in> consensus_value_property_decisions \<sigma>\<close> consensus_value_property_decisions_def consensus_value_property_is_decided_def 
    using \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> forward_consistency by fastforce
  have "\<sigma>'' \<in> futures \<sigma>'" 
    using \<open>\<sigma>'' \<in> \<Sigma>t \<and> \<sigma>'' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> p \<in> consensus_value_property_decisions \<sigma>\<close>
    by auto
  hence "\<not> state_property_is_decided (state_property_not (naturally_corresponding_state_property p), \<sigma>')"
      (* NOTE: About the non-deterministicity, should we define this as safety? *)
      using backword_consistency \<open>state_property_is_decided (naturally_corresponding_state_property p, \<sigma>'')\<close>
      using \<open>\<sigma>'' \<in> \<Sigma>t \<and> \<sigma>'' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> p \<in> consensus_value_property_decisions \<sigma>\<close> by auto  
  then show "consensus_value_property_not p \<notin> consensus_value_property_decisions \<sigma>'"
    apply (simp add: consensus_value_property_decisions_def consensus_value_property_is_decided_def naturally_corresponding_state_property_def state_property_is_decided_def)
    using \<Sigma>t_def estimates_are_non_empty futures_def by fastforce   
qed

(* FIXME: Combine this with negation_is_not_decided_by_other_validator (skipped this because it is used in other places.) *)
lemma (in Protocol) n_party_consensus_safety :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> (\<forall> p \<in> \<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}. 
           (\<lambda>c. (\<not> p c)) \<notin> \<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set})"
  apply (rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma>_set p
  assume "\<sigma>_set \<subseteq> \<Sigma>t" and "finite \<sigma>_set" and "is_faults_lt_threshold (\<Union>\<sigma>_set)" and "p \<in> \<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}"
  and "(\<lambda>c. (\<not> p c)) \<in> \<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}"
  hence "\<exists> \<sigma>. \<sigma> \<in> \<Sigma>t \<and> \<sigma> \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}"
    using n_party_common_futures_exists by meson
  then obtain \<sigma>'' where "\<sigma>'' \<in> \<Sigma>t \<and> \<sigma>'' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}" by auto
  hence "state_property_is_decided (naturally_corresponding_state_property p, \<sigma>'')" 
    using \<open>p \<in> \<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}\<close> consensus_value_property_decisions_def consensus_value_property_is_decided_def 
    using \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> forward_consistency by fastforce
  have "state_property_is_decided (naturally_corresponding_state_property (\<lambda>c. (\<not> p c)), \<sigma>'')" 
    using \<open>(\<lambda>c. (\<not> p c)) \<in> \<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}\<close> consensus_value_property_decisions_def consensus_value_property_is_decided_def 
    using \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> forward_consistency \<open>\<sigma>'' \<in> \<Sigma>t \<and> \<sigma>'' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> by fastforce
  then show False
    using \<open>state_property_is_decided (naturally_corresponding_state_property p, \<sigma>'')\<close>
    apply (simp add: state_property_is_decided_def naturally_corresponding_state_property_def)
    by (meson \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma>'' \<in> \<Sigma>t \<and> \<sigma>'' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> estimates_are_non_empty monotonic_futures order_refl subsetCE)
qed


lemma (in Protocol) two_party_consensus_safety_for_consensus_value_property :
  "\<forall> \<sigma>1 \<sigma>2. \<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t
  \<longrightarrow> is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)
  \<longrightarrow> consensus_value_property_is_decided (p, \<sigma>1) 
  \<longrightarrow> \<not> consensus_value_property_is_decided (consensus_value_property_not p, \<sigma>2)"
  apply (rule, rule, rule, rule, rule)
proof -
  fix \<sigma>1 \<sigma>2
  have two_party: "\<forall> \<sigma>1 \<sigma>2. {\<sigma>1, \<sigma>2} \<subseteq> \<Sigma>t
        \<longrightarrow> is_faults_lt_threshold (\<Union> {\<sigma>1, \<sigma>2})
        \<longrightarrow> p \<in> consensus_value_property_decisions \<sigma>1 
            \<longrightarrow> consensus_value_property_not p \<notin> consensus_value_property_decisions \<sigma>2"
    using negation_is_not_decided_by_other_validator
    by (meson finite.emptyI finite.insertI order_refl)
  assume "\<sigma>1 \<in> \<Sigma>t \<and> \<sigma>2 \<in> \<Sigma>t" and "is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)" and "consensus_value_property_is_decided (p, \<sigma>1)"
  then show "\<not> consensus_value_property_is_decided (consensus_value_property_not p, \<sigma>2)"  
    using two_party
    apply (simp add: consensus_value_property_decisions_def)
    by blast
qed    

lemma (in Protocol) n_party_consensus_safety_for_power_set_of_decisions :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> (\<forall> \<sigma> p_set. \<sigma> \<in> \<sigma>_set \<and> p_set \<in> Pow (\<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}) - {\<emptyset>} 
      \<longrightarrow> (\<lambda>c. \<not> (\<forall> p \<in> p_set. p c)) \<notin> consensus_value_property_decisions \<sigma>)"
  apply (rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma>_set \<sigma> p_set
  assume "\<sigma>_set \<subseteq> \<Sigma>t" and "finite \<sigma>_set" and "is_faults_lt_threshold (\<Union>\<sigma>_set)" 
  and "\<sigma> \<in> \<sigma>_set \<and> p_set \<in> Pow (\<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}) - {\<emptyset>}"
  and "(\<lambda>c. \<not> (\<forall> p \<in> p_set. p c)) \<in> consensus_value_property_decisions \<sigma>"
  hence "\<exists> \<sigma>. \<sigma> \<in> \<Sigma>t \<and> \<sigma> \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}"
    using n_party_common_futures_exists by meson
  then obtain \<sigma>' where "\<sigma>' \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}" by auto
  hence "\<forall> p \<in> p_set. \<exists> \<sigma>'' \<in> \<sigma>_set. state_property_is_decided (naturally_corresponding_state_property p, \<sigma>'')"
    using  \<open>\<sigma> \<in> \<sigma>_set \<and> p_set \<in> Pow (\<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}) - {\<emptyset>}\<close>
    apply (simp add: consensus_value_property_decisions_def consensus_value_property_is_decided_def)
    by blast
  have "\<forall> \<sigma>'' \<in> \<sigma>_set. \<sigma>' \<in> futures \<sigma>''"
    using \<open>\<sigma>' \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> by blast
  hence "\<forall> p \<in> p_set. state_property_is_decided (naturally_corresponding_state_property p, \<sigma>')"
    using forward_consistency \<open>\<forall> p \<in> p_set. \<exists> \<sigma>'' \<in> \<sigma>_set. state_property_is_decided (naturally_corresponding_state_property p, \<sigma>'')\<close> 
    by (meson \<open>\<sigma>' \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> subsetCE)
  hence "state_property_is_decided (naturally_corresponding_state_property (\<lambda>c. \<forall> p \<in> p_set. p c), \<sigma>')"
    apply (simp add: naturally_corresponding_state_property_def state_property_is_decided_def)
    by auto
  then show False
    using \<open>(\<lambda>c. \<not> (\<forall> p \<in> p_set. p c)) \<in> consensus_value_property_decisions \<sigma>\<close>  
    apply (simp add: consensus_value_property_decisions_def  consensus_value_property_is_decided_def naturally_corresponding_state_property_def  state_property_is_decided_def)
    using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<sigma>_set \<and> p_set \<in> Pow (\<Union> {consensus_value_property_decisions \<sigma>' | \<sigma>'. \<sigma>' \<in> \<sigma>_set}) - {\<emptyset>}\<close> \<open>\<sigma>' \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Inter> {futures \<sigma> | \<sigma>. \<sigma> \<in> \<sigma>_set}\<close> estimates_are_non_empty monotonic_futures by fastforce
qed

end
