theory SafetyOracle

imports Main CBCCasper ConsensusSafety

begin

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* Definition 7.1 *)
fun later :: "(message * message) \<Rightarrow> bool"
  where
    "later (m1, m2) = (m2 \<in> justification m1)"

(* Definition 7.2 *)
fun (in Protocol) from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender (v, \<sigma>) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v}"
     
(* Definition 7.3 *)
fun (in Protocol) later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = {m' \<in> M. m \<in> \<sigma> \<and> sender m' = v \<and> later (m', m)}"
 
(* Definition 7.4 *)
fun (in Protocol) latest_messages :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages (\<sigma>, v) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v \<and> later_from (m, v, \<sigma>) = \<emptyset>}"

(* Definition 7.5 *)
fun (in Protocol) latest_messages_from_honest_validators :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages_from_honest_validators (\<sigma>, v) = 
      (if v \<in> equivocating_validators \<sigma> then \<emptyset> else latest_messages (\<sigma>, v))"

(* Definition 7.6 *)
fun (in Protocol) latest_estimates_from_honest_validators:: "(state * validator) \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_honest_validators (\<sigma>, v) = 
      {est m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

lemma (in Protocol) latest_estimates_from_honest_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates_from_honest_validators (\<sigma>, v) \<subseteq> C"
  using M_type by auto

(* Definition 7.7 *)
fun (in Protocol) latest_justifications_from_honest_validators :: "(state * validator) \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators (\<sigma>, v) = 
      {justification m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

lemma (in Protocol) latest_justifications_from_honest_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_justifications_from_honest_validators (\<sigma>, v) \<subseteq> \<Sigma>"
  using M_type by auto

(* Definition 7.8 *)
fun (in Protocol) agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators (p, \<sigma>) = {v \<in> V. \<forall> c \<in> C. c \<in> latest_estimates_from_honest_validators (\<sigma>, v) \<and> p c}"

(* Definition 7.9 *)
fun (in Protocol) disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators (p, \<sigma>) = {v \<in> V. \<exists> c \<in> C. c \<in> latest_estimates_from_honest_validators (\<sigma>, v) \<and> \<not> p c}"

(* Definition 7.10 *)
definition (in Protocol) weight_measure :: "validator set \<Rightarrow> real"
  where
    "weight_measure v_set = sum W v_set"

(* Definition 7.11 *)
fun (in Protocol) is_majority :: "(validator set * state) \<Rightarrow> bool"
  where
    "is_majority (v_set, \<sigma>) = (weight_measure v_set > (weight_measure V - weight_measure (equivocating_validators \<sigma>)) div 2)"
   
(* Definition 7.12 *)
definition (in Protocol) is_majority_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven p = (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> is_majority (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> c \<in> \<epsilon> \<sigma> \<and> p c)"

(* Definition 7.13 *)
definition (in Protocol) is_max_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven p =
      (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (disagreeing_validators (p, \<sigma>)) \<longrightarrow> c \<in> \<epsilon> \<sigma> \<and> p c)"

(* Definition 7.14 *)
fun (in Protocol) later_disagreeing_messages :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_messages (p, m, v, \<sigma>) = {m' \<in> M. m' \<in> later_from (m, v, \<sigma>) \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* `the_elem` is built-in  *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)
fun (in Protocol) is_clique :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique (v_set, p, \<sigma>) = 
     (\<forall> v \<in> v_set. v_set \<subseteq> agreeing_validators (p, the_elem (latest_justifications_from_honest_validators (\<sigma>, v)))
     \<and>  (\<forall>  v' \<in> v_set. later_disagreeing_messages (p, the_elem (latest_messages_from_honest_validators (the_elem (latest_justifications_from_honest_validators (\<sigma>, v)), v')), v', \<sigma>) = \<emptyset>))"


(* Section 7.3: Cliques Survive Messages from Validators Outside Clique *)

(* Definition 7.17 *)
abbreviation (in Protocol) minimal_transitions :: "(state * state) set"
  where
    "minimal_transitions \<equiv> {(\<sigma>, \<sigma>') | \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t \<and> is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>'
      \<and> (\<nexists> \<sigma>''. \<sigma>'' \<in> \<Sigma> \<and> is_future_state (\<sigma>'', \<sigma>) \<and> is_future_state (\<sigma>', \<sigma>'') \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>'' \<noteq> \<sigma>')}"

(* A minimal transition corresponds to receiving a single new message with justification drawn from the initial
protocol state *)
definition immediately_next_message where
  "immediately_next_message = (\<lambda>(\<sigma>,m). justification m \<subseteq> \<sigma> \<and> m \<notin> \<sigma>)"

lemma (in Protocol) message_cannot_justify_itself: "\<nexists>m. m \<in> M \<longrightarrow> m \<in> justification m"
  sorry

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
  "\<forall>\<sigma>\<in>\<Sigma>. \<forall>\<sigma>'\<in>\<Sigma>. is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>' \<longrightarrow> (\<exists>m \<in> (\<sigma>'-\<sigma>). justification m \<subseteq> \<sigma>)"
  oops  

lemma (in Protocol) no_missing_message: "\<forall>\<sigma>\<in>\<Sigma>. \<forall>m\<in>\<sigma>. \<forall>m'\<in>justification m. m' \<in> \<sigma>"
  using state_is_in_pow_M_i by fastforce

lemma (in Protocol) minimal_transition_implies_recieving_a_single_message :
  "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>, \<sigma>') \<in> minimal_transitions  \<longrightarrow> is_singleton (\<sigma>'- \<sigma>)"
  sorry

(* Lemma 11: Minimal transitions do not change Later_From for any non-sender *)
lemma (in Protocol) later_from_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m m'. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> (\<forall> v \<in> V - {sender m'}. later_from (m, v, \<sigma>) = later_from (m, v, \<sigma>'))"
  apply (rule, rule, rule, rule, rule, rule)
proof-
  fix \<sigma> \<sigma>' m m' v
  assume "(\<sigma>, \<sigma>') \<in> {(\<sigma>, \<sigma>') |\<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t \<and> is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>' \<and> (\<nexists>\<sigma>''. \<sigma>'' \<in> \<Sigma> \<and> is_future_state (\<sigma>'', \<sigma>) \<and> is_future_state (\<sigma>', \<sigma>'') \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>'' \<noteq> \<sigma>')}
    \<and> m' = the_elem (\<sigma>' - \<sigma>)"
  and "v \<in> V - {sender m'}"

  have "later_from (m,v,\<sigma>) = {m' \<in> \<sigma>. sender m' = v \<and> later(m',m)}"
    sorry
  also have "\<dots> = {m' \<in> \<sigma>. sender m' = v \<and> later(m',m)} \<union> \<emptyset>"
    by simp
  also have "\<dots> = {m' \<in> \<sigma>. sender m' = v \<and> later(m',m)} \<union> {m'' \<in> {m'}. sender m'' = v}"
  proof-
    have "{m'' \<in> {m'}. sender m'' = v} = \<emptyset>"
      using \<open>v \<in> V - {sender m'}\<close> by auto
    thus ?thesis
      by blast
  qed
  also have "\<dots> = {m' \<in> \<sigma>. sender m' = v \<and> later(m',m)} \<union> {m'' \<in> {m'}. sender m'' = v \<and> later(m',m)}"
  proof-
    have "sender m' = v \<Longrightarrow> later(m',m)"
      using \<open>v \<in> V - {sender m'}\<close> by auto
    thus ?thesis
      by blast
  qed
  also have "\<dots> = {m'' \<in> \<sigma> \<union> {m'}. sender m'' = v \<and> later(m'',m)}"
    by auto
  also have "\<dots> = {m'' \<in> \<sigma>'. sender m'' = v \<and> later(m'',m)}"
    sorry
  also have "\<dots> = later_from (m,v,\<sigma>')"
    sorry
  finally show "later_from (m, v, \<sigma>) = later_from (m, v, \<sigma>')"
    by simp
qed

(* Definition 7.18: One layer clique oracle threshold size *) 
fun (in Protocol) gt_threshold :: "(validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold (v_set, \<sigma>)
       = (weight_measure v_set > (weight_measure v_set) div 2 + t  - weight_measure (equivocating_validators \<sigma>))"

(* Definition 7.19: Clique oracle with 1 layers *)
fun (in Protocol) is_clique_oracle :: "(validator set * state * consensus_value_property) \<Rightarrow> bool"
  where
    "is_clique_oracle (v_set, \<sigma>, p)
       = (is_clique (v_set - (equivocating_validators \<sigma>), p, \<sigma>) \<and> gt_threshold (v_set - (equivocating_validators \<sigma>), \<sigma>))"

end