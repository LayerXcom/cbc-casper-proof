theory StateTransition

imports Main CBCCasper ConsensusSafety

begin


(* Definition 7.17 *)
abbreviation (in Protocol) minimal_transitions :: "(state * state) set"
  where
    "minimal_transitions \<equiv> {(\<sigma>, \<sigma>') | \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t \<and> is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>'
      \<and> (\<nexists> \<sigma>''. \<sigma>'' \<in> \<Sigma> \<and> is_future_state (\<sigma>'', \<sigma>) \<and> is_future_state (\<sigma>', \<sigma>'') \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>'' \<noteq> \<sigma>')}"

(* A minimal transition corresponds to receiving a single new message with justification drawn from the initial
protocol state *)
definition immediately_next_message where
  "immediately_next_message = (\<lambda>(\<sigma>,m). justification m \<subseteq> \<sigma> \<and> m \<notin> \<sigma>)"

lemma (in Protocol) state_transition_by_immediately_next_message_induction: "\<forall>n\<ge>1. \<forall>\<sigma>\<in>\<Sigma>_i (V,C,\<epsilon>) n. \<forall>m\<in>M_i (V,C,\<epsilon>) n. immediately_next_message (\<sigma>,m) \<longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>_i (V,C,\<epsilon>) (n+1)"
  apply (rule, rule, rule, rule, rule)
proof-
  fix n \<sigma> m
  assume "1 \<le> n" "\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n" "m \<in> M_i (V, C, \<epsilon>) n" "immediately_next_message (\<sigma>, m)"

  have "\<exists>n'. n = Suc n'"
    using \<open>1 \<le> n\<close> old.nat.exhaust by auto
  hence si: "\<Sigma>_i (V,C,\<epsilon>) n = {\<sigma> \<in> Pow (M_i (V,C,\<epsilon>) (n - 1)). \<forall> m. m \<in> \<sigma> \<longrightarrow> justification m \<subseteq> \<sigma>}"
    by force

  hence "\<Sigma>_i (V,C,\<epsilon>) (n+1) = {\<sigma> \<in> Pow (M_i (V,C,\<epsilon>) n). \<forall> m. m \<in> \<sigma> \<longrightarrow> justification m \<subseteq> \<sigma>}"
    by force

  have "justification m \<subseteq> \<sigma>"
    using immediately_next_message_def
    by (metis (no_types, lifting) \<open>immediately_next_message (\<sigma>, m)\<close> case_prod_conv)
  hence "justification m \<subseteq> \<sigma> \<union> {m}"
    by blast
  moreover have "\<And>m'. m' \<in> \<sigma> \<Longrightarrow> justification m' \<subseteq> \<sigma>"
    using \<open>\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n\<close> si by blast
  hence"\<And>m'. m' \<in> \<sigma> \<Longrightarrow> justification m' \<subseteq> \<sigma> \<union> {m}"
    by auto
  ultimately have "\<And>m'. m' \<in> \<sigma> \<union> {m} \<Longrightarrow> justification m \<subseteq> \<sigma>"
    using \<open>justification m \<subseteq> \<sigma>\<close> by blast

  have "{m} \<in> Pow (M_i (V,C,\<epsilon>) n)"
    using \<open>m \<in> M_i (V, C, \<epsilon>) n\<close> by auto
  moreover have "\<sigma> \<in> Pow (M_i (V,C,\<epsilon>) (n-1))"
    using \<open>\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n\<close> si by auto
  hence "\<sigma> \<in> Pow (M_i (V,C,\<epsilon>) n)"
    using Mi_monotonic
    by (metis (full_types) PowD PowI Suc_eq_plus1 \<open>\<exists>n'. n = Suc n'\<close> diff_Suc_1 subset_iff)
  ultimately have "\<sigma> \<union> {m} \<in> Pow (M_i (V,C,\<epsilon>) n)"
    by blast

  show "\<sigma> \<union> {m} \<in> \<Sigma>_i (V, C, \<epsilon>) (n + 1)"
    using \<open>\<And>m'. m' \<in> \<sigma> \<Longrightarrow> justification m' \<subseteq> \<sigma> \<union> {m}\<close> \<open>\<sigma> \<union> {m} \<in> Pow (M_i (V, C, \<epsilon>) n)\<close> \<open>justification m \<subseteq> \<sigma> \<union> {m}\<close> by auto
qed

lemma (in Protocol) state_transition_by_immediately_next_message_at_n: "\<forall>\<sigma>\<in>\<Sigma>_i (V,C,\<epsilon>) n. \<forall>m\<in>M_i (V,C,\<epsilon>) n. immediately_next_message (\<sigma>,m) \<longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>_i (V,C,\<epsilon>) (n+1)"
  apply (cases n)
  apply auto[1]
  using state_transition_by_immediately_next_message_induction
  by (metis le_add1 plus_1_eq_Suc)

lemma (in Protocol) state_differences_have_immediately_next_messages: 
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> \<sigma>'\<in> \<Sigma>. is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>' \<longrightarrow> (\<exists> m \<in> \<sigma>'-\<sigma>. immediately_next_message (\<sigma>, m))"
  apply (simp add: immediately_next_message_def)
  apply (rule, rule, rule)
proof -
  fix \<sigma> \<sigma>'
  assume "\<sigma> \<in> \<Sigma>"
  assume "\<sigma>' \<in> \<Sigma>"
  assume "\<sigma> \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>'"
  show "\<exists> m \<in> \<sigma>' - \<sigma>. justification m \<subseteq> \<sigma>"
  proof (rule ccontr)
    assume "\<not> (\<exists> m \<in> \<sigma>' - \<sigma>. justification m \<subseteq> \<sigma>)"
    have "\<forall> m \<in> \<sigma>' - \<sigma>. \<exists> m' \<in> justification m. m' \<in> \<sigma>' - \<sigma>"
      using \<open>\<not> (\<exists>m\<in>\<sigma>' - \<sigma>. justification m \<subseteq> \<sigma>)\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> state_is_in_pow_M_i by fastforce
    then have "\<forall> m \<in> \<sigma>' - \<sigma>. \<exists> m' \<in> justification m. m' \<in> \<sigma>' - \<sigma> \<and> m \<noteq> m'"
      using \<open>\<sigma>' \<in> \<Sigma>\<close> irreflexivity_of_justifications state_is_subset_of_M by fastforce 
    show False
      sorry
  qed
qed

lemma (in Protocol) minimal_transition_implies_recieving_a_single_message :
  "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>, \<sigma>') \<in> minimal_transitions  \<longrightarrow> is_singleton (\<sigma>'- \<sigma>)"
  sorry

end