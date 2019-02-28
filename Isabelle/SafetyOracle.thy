theory SafetyOracle

imports Main CBCCasper LatestMessage StateTransition ConsensusSafety

begin

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* NOTE: Definition 7.1 is defined as `justified` *)
(* NOTE: Definition 7.2 is duplicate of definition 4.3 *)
(* NOTE: Definition 7.3 is duplicate of definition 4.5 *)
(* NOTE: Definition 7.4 is duplicate of definition 4.6 *)
(* NOTE: Definition 7.5 is duplicate of definition 4.11 *)
(* NOTE: Definition 7.6 is duplicate of definition 4.13 *)

(* Definition 7.7 *)
fun latest_justifications_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> state set"
  where
    "latest_justifications_from_non_equivocating_validators \<sigma> v = 
      {justification m | m. m \<in> latest_messages_from_non_equivocating_validators \<sigma> v}"

lemma (in Protocol) latest_justifications_from_non_equivocating_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_justifications_from_non_equivocating_validators \<sigma> v \<subseteq> \<Sigma>"
  using M_type latest_messages_from_non_equivocating_validators_type by auto

(* Definition 7.8 *)
(* NOTE: Modified from the original draft with observed_non_equivocating_validators *)
definition  agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators  = (\<lambda>(p, \<sigma>).{v \<in> observed_non_equivocating_validators \<sigma>. \<forall> c \<in> latest_estimates_from_non_equivocating_validators \<sigma> v. p c})"

lemma (in Protocol) agreeing_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (p, \<sigma>) \<subseteq> V"
  apply (simp add: observed_non_equivocating_validators_def agreeing_validators_def)
  using observed_type_for_state by auto

lemma (in Protocol) agreeing_validators_finite :
  "\<forall> \<sigma> \<in> \<Sigma>. finite (agreeing_validators (p, \<sigma>))"
  by (meson V_type agreeing_validators_type rev_finite_subset)

(* Definition 7.9 *)
definition disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators  = (\<lambda>(p, \<sigma>). {v \<in> observed_non_equivocating_validators \<sigma>. \<exists> c \<in> latest_estimates_from_non_equivocating_validators \<sigma> v. \<not> p c})"

lemma (in Protocol) disagreeing_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. disagreeing_validators (p, \<sigma>) \<subseteq> V"
  apply (simp add: observed_non_equivocating_validators_def disagreeing_validators_def)
  using observed_type_for_state by auto


(* Definition 7.11 *)
definition (in Params) is_majority :: "(validator set * state) \<Rightarrow> bool"
  where
    "is_majority  = (\<lambda>(v_set, \<sigma>). (weight_measure v_set > (weight_measure (V - equivocating_validators \<sigma>)) div 2))"
   
(* Definition 7.12 *)
definition (in Protocol) is_majority_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven p = (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> is_majority (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c))"

(* Definition 7.13 *)
definition (in Protocol) is_max_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven p =
      (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (disagreeing_validators (p, \<sigma>)) \<longrightarrow> c \<in> \<epsilon> \<sigma> \<and> p c)"

(* Definition 7.14 *)
definition later_disagreeing_messages :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_messages = (\<lambda>(p, m, v, \<sigma>).{m' \<in> later_from (m, v, \<sigma>). \<not> p (est m')})"

lemma (in Protocol) later_disagreeing_messages_type :
  "\<forall> p \<sigma> v m. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) \<subseteq> M"
  unfolding later_disagreeing_messages_def
  using later_from_type_for_state by auto

(* Definition 7.15 *)
(* `the_elem` is built-in  *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)
definition is_clique :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique = (\<lambda>(v_set, p, \<sigma>). 
     (\<forall> v \<in> v_set. v_set \<subseteq> agreeing_validators (p, the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v))
     \<and>  (\<forall>  v' \<in> v_set. later_disagreeing_messages (p, the_elem (latest_messages_from_non_equivocating_validators (the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)))"


(* Section 7.3: Cliques Survive Messages from Validators Outside Clique *)

(* Lemma 11: Minimal transitions do not change Later_From for any non-sender *)
lemma (in Protocol) later_from_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m \<in> M
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> later_from (m, v, \<sigma>) = later_from (m, v, \<sigma>')"
  apply (rule, rule, rule, rule, rule, rule, rule, rule)
proof-
  fix \<sigma> \<sigma>' m m' v
  assume "(\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m \<in> M"
  assume "m' = the_elem (\<sigma>' - \<sigma>)"
  assume "v \<in> V - {sender m'}"

  have "later_from (m,v,\<sigma>) = {m'' \<in> \<sigma>. sender m'' = v \<and> justified m m''}"
    apply (simp add: later_from_def from_sender_def later_def)
    by auto
  also have "\<dots> = {m'' \<in> \<sigma>. sender m'' = v \<and> justified m m''} \<union> \<emptyset>"
    by auto    
  also have "\<dots> = {m'' \<in> \<sigma>. sender m'' = v \<and> justified m m''} \<union> {m'' \<in> {m'}. sender m'' = v}"
  proof-
    have "{m'' \<in> {m'}. sender m'' = v} = \<emptyset>"
      using \<open>v \<in> V - {sender m'}\<close> by auto
    thus ?thesis
      by blast
  qed
  also have "\<dots> = {m'' \<in> \<sigma>. sender m'' = v \<and> justified m m''} \<union> {m'' \<in> {m'}. sender m'' = v \<and> justified m m''}"
  proof-
    have "sender m' = v \<Longrightarrow> justified m m'"
      using \<open>v \<in> V - {sender m'}\<close> by auto
    thus ?thesis
      by blast
  qed
  also have "\<dots> = {m'' \<in> \<sigma> \<union> {m'}. sender m'' = v \<and> justified m m''}"
    by auto
  also have "\<dots> = {m'' \<in> \<sigma>'. sender m'' = v \<and> justified m m''}"
  proof -
    have "\<sigma>' =  \<sigma> \<union> {m'}"
      using \<open>(\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m \<in> M\<close> \<open>m' = the_elem (\<sigma>' - \<sigma>)\<close> minimal_transitions_reconstruction by auto 
    then show ?thesis
      by auto
  qed
  then have "\<dots> = later_from (m,v,\<sigma>')"
    apply (simp add: later_from_def from_sender_def later_def)
    by auto
  then show "later_from (m, v, \<sigma>) = later_from (m, v, \<sigma>')"
    using \<open>{m'' \<in> \<sigma> \<union> {m'}. sender m'' = v \<and> justified m m''} = {m'' \<in> \<sigma>'. sender m'' = v \<and> justified m m''}\<close> calculation by auto
qed

(* Lemma 12: Minimal transitions do not change equivocation status for any non-sender *)
lemma (in Protocol) equivocation_status_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> v \<in> equivocating_validators \<sigma> \<longleftrightarrow> v \<in> equivocating_validators \<sigma>'"
  oops

(* Lemma 13: Minimal transitions do not change latest messages for any non-sender. *)
lemma (in Protocol) latest_messages_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> latest_messages_from_non_equivocating_validators \<sigma> v = latest_messages_from_non_equivocating_validators \<sigma>' v"
  oops

(* Lemma 14 (Minimal transitions do not change latest justification for any non-sender). *)
lemma (in Protocol) latest_justificationss_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> latest_justifications_from_non_equivocating_validators \<sigma> v = latest_justifications_from_non_equivocating_validators \<sigma>' v"
  oops

(* Lemma 15 (Minimal transitions do not change Later Disagreeing for any non-sender). *)
lemma (in Protocol) later_disagreeing_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m \<in> M
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) = later_disagreeing_messages (p, m, v, \<sigma>')"
  oops


(* Lemma 16 (Minimal transition from outside clique maintains clique). *)
lemma (in Protocol) clique_not_affected_by_minimal_transitions_outside_clique :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> is_clique (v_set, p, \<sigma>) = is_clique (v_set, p, \<sigma>')"
  oops


(* 7.4 Majority Cliques Survive Honest Messages from Validators in Clique *)
(* 7.4.1 New messages at least leaves a smaller clique behind *)

(* Lemma 17 (Free sub-clique)  *)
lemma (in Protocol) free_sub_clique :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> is_clique (v_set, p, \<sigma>) = is_clique (v_set - {sender m'}, p, \<sigma>')"
  oops

(* 7.4.2 Non-equivocating messages from clique members see clique agree *)
(* Lemma 18 (Later messages from a non-equivocating validator include all earlier messages) *)
(* NOTE: \<sigma>2 is not a state, just a set of messages. *)
lemma (in Protocol) later_messages_from_non_equivocating_validator_include_all_earlier_messages :
  "\<forall> v \<sigma> \<sigma>1 \<sigma>2. \<sigma> \<in> \<Sigma> \<and> \<sigma>1 \<in> \<Sigma> \<and> \<sigma>1 \<subseteq> \<sigma> \<and> \<sigma>2 \<subseteq> \<sigma> \<and> \<sigma>1 \<inter> \<sigma>2 = \<emptyset>
  \<longrightarrow> (\<forall> m1 \<in> \<sigma>1. sender(m1) = v \<longrightarrow> (\<forall> m2 \<in> \<sigma>2. sender(m2) = v \<longrightarrow> m1 \<in> justification(m2)))"
  oops

(* Lemma 19 (m' is its sender's latest message in \<sigma>’). *)
lemma (in Protocol) message_between_minimal_transition_is_latest_message :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> m' = the_elem (latest_messages_from_non_equivocating_validators \<sigma>' v)"
  oops

(* Lemma 20 (Latest honest messages from non-equivocating messages are either the same as in their previous
latest message, or later) *)
lemma (in Protocol) latest_message_from_non_equivocating_validator_is_previous_latest_or_later:
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma> \<and> v \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> the_elem (latest_messages_from_non_equivocating_validators (justification m') v) 
       = the_elem (latest_messages_from_non_equivocating_validators (the_elem (latest_justifications_from_non_equivocating_validators \<sigma> (sender m'))) v)
      \<or> justified (the_elem (latest_messages_from_non_equivocating_validators (the_elem (latest_justifications_from_non_equivocating_validators \<sigma> (sender m'))) v)) 
                  (the_elem (latest_messages_from_non_equivocating_validators (justification m') v))"
  oops

(* Lemma 21. *)
lemma (in Protocol) justified_message_exists_in_later_from:
  "\<forall> \<sigma> m1 m2. \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> \<sigma>
  \<longrightarrow> justified m1 m2 \<longrightarrow> m2 \<in> later_from (m1, sender m1, \<sigma>)"
  apply (simp add: later_from_def later_def from_sender_def)
  oops

(* Lemma 22. *)

(* Lemma 23 (Non-equivocating messages from clique members see clique agree). *)
lemma (in Protocol) non_equivocating_message_from_clique_see_clique_agreeing :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> is_clique (v_set, p, \<sigma>) \<and> sender m' \<in> v_set \<and> sender m' \<notin> equivocating_validators \<sigma>' 
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, justification m')"
  oops

(* 7.4.3 Non-equivocating messages from majority clique members agree *)

(* Lemma 24 (New messages from majority clique members agree) *)
lemma (in Protocol) new_message_from_majority_clique_see_members_agreeing :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> is_clique (v_set, p, \<sigma>) \<and> sender m' \<in> v_set \<and> sender m' \<notin> equivocating_validators \<sigma>'
      \<and> (\<forall> v \<in> v_set. is_majority (v_set, the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v))) 
  \<longrightarrow> sender m' \<in> agreeing_validators (p, justification m')"
  oops

(* 7.4.4 Honest messages from majority clique members do not break the clique *)

(* Lemma 25 *)
lemma (in Protocol) latest_message_in_justification_of_new_message_is_latest_message :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> the_elem (latest_messages_from_non_equivocating_validators (justification m') (sender m')) = the_elem (latest_messages_from_non_equivocating_validators \<sigma> (sender m'))"
  oops


(* Lemma 26 *)
lemma (in Protocol) latest_message_justified_by_new_message :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> justified (the_elem (latest_messages_from_non_equivocating_validators \<sigma> (sender m'))) m'"
  oops

(* Lemma 27 (Nothing later than latest honest message).  *)
lemma (in Protocol) nothing_later_than_latest_honest_message :
  "\<forall> v \<sigma> m. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<and> m \<in> M
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> later_from (the_elem (latest_messages_from_non_equivocating_validators \<sigma> v), v, \<sigma>) =  \<emptyset>"
  oops

(* Lemma 28 (Later messages for sender is just the new message). *)
lemma (in Protocol) later_messages_for_sender_is_new_message :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> later_from (the_elem (latest_messages_from_non_equivocating_validators \<sigma> (sender m')), sender m', \<sigma>') =  {m'}"
  oops

(* Lemma 29 (Later disagreeing is monotonic) *)
lemma (in Protocol) later_disagreeing_is_monotonic:
  "\<forall> v \<sigma> m1 m2. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> M
  \<longrightarrow> justified m1 m2
  \<longrightarrow> later_disagreeing_messages (p, m2, v, \<sigma>) \<subseteq> later_disagreeing_messages (p, m1, v, \<sigma>)"
  oops

(* Lemma 30 *)
lemma (in Protocol) empty_later_disagreeing_messages_in_new_message :
  "\<forall> \<sigma> \<sigma>' m' v_set v p. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V \<and> v \<in> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>' 
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>
  \<longrightarrow> later_disagreeing_messages (p, (the_elem (latest_messages_from_non_equivocating_validators (the_elem (latest_justifications_from_non_equivocating_validators \<sigma> (sender m'))) v)), v, \<sigma>) = \<emptyset>
  \<longrightarrow> later_disagreeing_messages (p, (the_elem (latest_messages_from_non_equivocating_validators (justification m') v)), v, \<sigma>) = \<emptyset>"
  oops

(* Lemma 31 (New non-equivocating latest messages from members of majority clique don’t break the clique) *)
lemma (in Protocol) clique_not_affected_by_minimal_transitions_outside_clique :
  "\<forall> \<sigma> \<sigma>' m' v_set p. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> is_clique (v_set, p, \<sigma>) \<and> sender m' \<in> v_set \<and> sender m' \<notin> equivocating_validators \<sigma>'
      \<and> (\<forall> v \<in> v_set. is_majority (v_set, the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v))) 
  \<longrightarrow> is_clique (v_set, p, \<sigma>')"
  oops


(* 7.5 Equivocations from Validators in Clique do not break cliques *)

(* Definition 7.18: One layer clique oracle threshold size *) 
definition (in Params) gt_threshold :: "(validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold 
       = (\<lambda>(v_set, \<sigma>).(weight_measure v_set > (weight_measure V) div 2 + t  - weight_measure (equivocating_validators \<sigma>)))"

(* Lemma 32 *)
lemma (in Protocol) gt_threshold_imps_majority_for_any_validator :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V
  \<longrightarrow> gt_threshold (v_set, \<sigma>) 
  \<longrightarrow> (\<forall> v \<in> v_set. is_majority (v_set, the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v)))"
  oops

(* Definition 7.19: Clique oracle with 1 layers *)
definition (in Params) is_clique_oracle :: "(validator set * state * consensus_value_property) \<Rightarrow> bool"
  where
    "is_clique_oracle 
       = (\<lambda>(v_set, \<sigma>, p). (is_clique (v_set - (equivocating_validators \<sigma>), p, \<sigma>) \<and> gt_threshold (v_set - (equivocating_validators \<sigma>), \<sigma>)))"

(* Lemma 33 (Clique oracles preserved over minimal transitions from validators not in clique). *)
lemma (in Protocol) clique_oracles_preserved_over_minimal_transitions_from_validators_not_in_clique :
  "\<forall> \<sigma> \<sigma>' m' v_set p. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> v_set - equivocating_validators \<sigma>
      \<and> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>', p)"
  oops

(* Lemma 34 (Clique oracles preserved over minimal transitions from non-equivocating validators) *)
lemma (in Protocol) clique_oracles_preserved_over_minimal_transitions_from_non_equivocating_validator :
  "\<forall> \<sigma> \<sigma>' m' v_set p. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<in> v_set - equivocating_validators \<sigma> \<and> sender m' \<notin> equivocating_validators \<sigma>'
      \<and> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>', p)"
  oops

(* Lemma 35 (Clique oracles preserved over minimal transitions from non-equivocating validators) *)
lemma (in Protocol) clique_oracles_preserved_over_minimal_transitions_from_equivocating_validator :
  "\<forall> \<sigma> \<sigma>' m' v_set p. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<in> v_set - equivocating_validators \<sigma> \<and> sender m' \<in> equivocating_validators \<sigma>'
      \<and> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>', p)"
  oops

(* Lemma 36 (Clique oracles preserved over minimal transitions) *)
lemma (in Protocol) clique_oracles_preserved_over_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m' v_set p. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>', p)"
  oops

(* Lemma 37 *)
lemma (in Protocol) clique_imps_everyone_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> is_clique (v_set, p, \<sigma>) 
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, \<sigma>)"
  sorry

(* Lemma 37 *)
lemma (in Protocol) threshold_sized_clique_imps_estimator_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> is_clique (v_set - equivocating_validators \<sigma>, p, \<sigma>) \<and> gt_threshold (v_set - equivocating_validators \<sigma>, \<sigma>) 
  \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c)"
  apply (rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma> v_set p c
  assume  "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V"
  and "finite v_set"
  and "is_majority_driven p"
  and "is_clique (v_set - equivocating_validators \<sigma>, p, \<sigma>) \<and> gt_threshold (v_set - equivocating_validators \<sigma>, \<sigma>)"
  and "c \<in> \<epsilon> \<sigma>"
  then have "v_set - equivocating_validators \<sigma> \<subseteq> agreeing_validators (p, \<sigma>)" 
    using clique_imps_everyone_agreeing
    by (meson Diff_subset \<Sigma>t_is_subset_of_\<Sigma> subsetCE subset_trans)
  then have "weight_measure (v_set - equivocating_validators \<sigma>) \<le> weight_measure (agreeing_validators (p, \<sigma>))"
    using agreeing_validators_finite equivocating_validators_def weight_measure_comparison_strict_subset_gte
          \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> \<open>finite v_set\<close> by auto
  have "weight_measure (v_set - equivocating_validators \<sigma>) > (weight_measure V) div 2 + t  - weight_measure (equivocating_validators \<sigma>)"
    using \<open>is_clique (v_set - equivocating_validators \<sigma>, p, \<sigma>) \<and> gt_threshold (v_set - equivocating_validators \<sigma>, \<sigma>)\<close>
    unfolding gt_threshold_def by simp
  then have "weight_measure (v_set - equivocating_validators \<sigma>) > (weight_measure V) div 2"
    using  \<Sigma>t_def \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> equivocation_fault_weight_def is_faults_lt_threshold_def 
    by auto
  then have "weight_measure (v_set - equivocating_validators \<sigma>) > (weight_measure (V - equivocating_validators \<sigma>)) div 2"
  proof - 
    have "finite (V - equivocating_validators \<sigma>)"
      using  V_type equivocating_validators_is_finite
      by simp
    moreover have "V - equivocating_validators \<sigma> \<subseteq> V"
      by (simp add: Diff_subset)
    ultimately have "(weight_measure V) div 2 \<ge> (weight_measure (V - equivocating_validators \<sigma>)) div 2" 
      using weight_measure_comparison_strict_subset_gte
      by (simp add: V_type)  
    then show ?thesis
      using \<open>weight_measure V / 2 < weight_measure (v_set - equivocating_validators \<sigma>)\<close> by linarith
  qed
  then have "weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (V - equivocating_validators \<sigma>) div 2" 
    using \<open>weight_measure (v_set - equivocating_validators \<sigma>) \<le> weight_measure (agreeing_validators (p, \<sigma>))\<close>
    by linarith  
  then show "p c"
    using \<open>is_majority_driven p\<close> unfolding is_majority_driven_def is_majority_def gt_threshold_def
    using \<open>c \<in> \<epsilon> \<sigma>\<close> 
    using M_i.simps \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> non_justifying_message_exists_in_M_0 by blast    
qed

(* Lemma 39 (Cliques exist in all futures) *)
lemma (in Protocol) clique_oracle_for_all_futures :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> \<sigma>' \<in> futures \<sigma>. is_clique_oracle (v_set, \<sigma>', p))"
  sorry

(* Lemma 40 (Clique oracle is a safety oracle) *)
lemma (in Protocol) clique_oracle_is_safety_oracle :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> is_majority_driven p
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> \<sigma>' \<in> futures \<sigma>. naturally_corresponding_state_property p \<sigma>')"    
  using clique_oracle_for_all_futures threshold_sized_clique_imps_estimator_agreeing
  apply (simp add: is_clique_oracle_def naturally_corresponding_state_property_def)
  by (metis (mono_tags, lifting) futures_def mem_Collect_eq)
  
end