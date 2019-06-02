theory CliqueOracle

imports Main CBCCasper LatestMessage StateTransition ConsensusSafety

begin

(* ###################################################### *)
(* Safety oracle *)
(* ###################################################### *)

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* NOTE: Definition 7.1 is defined as `justified` *)
(* NOTE: Definition 7.2 is duplicate of definition 4.3 *)
(* NOTE: Definition 7.3 is duplicate of definition 4.5 *)
(* NOTE: Definition 7.4 is duplicate of definition 4.6 *)
(* NOTE: Definition 7.5 is duplicate of definition 4.11 *)
(* NOTE: Definition 7.6 is duplicate of definition 4.13 *)
(* NOTE: Definition 7.7 is defined in LatestMessaege.thy*)


(* Definition 7.8 *)
definition agreeing :: "(consensus_value_property * state * validator) \<Rightarrow> bool"
  where
    "agreeing = (\<lambda>(p, \<sigma>, v). \<forall> c \<in> L_H_E \<sigma> v. p c)"

(* NOTE: Modified from the original draft with observed_non_equivocating_validators *)
definition agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators = (\<lambda>(p, \<sigma>).{v \<in> observed_non_equivocating_validators \<sigma>. agreeing  (p, \<sigma>, v)})"

lemma (in Protocol) agreeing_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (p, \<sigma>) \<subseteq> V"
  apply (simp add: observed_non_equivocating_validators_def agreeing_validators_def)
  using observed_type_for_state by auto

lemma (in Protocol) agreeing_validators_finite :
  "\<forall> \<sigma> \<in> \<Sigma>. finite (agreeing_validators (p, \<sigma>))"
  by (meson V_type agreeing_validators_type rev_finite_subset)

lemma (in Protocol) agreeing_validators_are_observed_non_equivocating_validators :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (p, \<sigma>) \<subseteq> observed_non_equivocating_validators \<sigma>"
  apply (simp add: agreeing_validators_def)
  by blast

lemma (in Protocol) agreeing_validators_are_not_equivocating :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (p, \<sigma>) \<inter> equivocating_validators \<sigma> = \<emptyset>"
  using agreeing_validators_are_observed_non_equivocating_validators
        observed_non_equivocating_validators_are_not_equivocating 
  by blast

(* Definition 7.9 *)
definition (in Params) disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators = (\<lambda>(p, \<sigma>). V - agreeing_validators (p, \<sigma>) - equivocating_validators \<sigma>)"

lemma (in Protocol) disagreeing_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. disagreeing_validators (p, \<sigma>) \<subseteq> V"
  apply (simp add: disagreeing_validators_def)
  by auto

lemma (in Protocol) disagreeing_validators_are_non_observed_or_not_agreeing :
  "\<forall> \<sigma> \<in> \<Sigma>. disagreeing_validators (p, \<sigma>) = {v \<in> V - equivocating_validators \<sigma>. v \<notin> observed \<sigma> \<or> (\<exists> c \<in> L_H_E \<sigma> v. \<not> p c)}"
  apply (simp add: disagreeing_validators_def agreeing_validators_def observed_non_equivocating_validators_def agreeing_def)
  by blast

lemma (in Protocol) disagreeing_validators_include_not_agreeing_validators :
  "\<forall> \<sigma> \<in> \<Sigma>. {v \<in> V - equivocating_validators \<sigma>. \<exists> c \<in> L_H_E \<sigma> v. \<not> p c} \<subseteq> disagreeing_validators (p, \<sigma>)"
  using disagreeing_validators_are_non_observed_or_not_agreeing by blast

lemma (in Protocol) weight_measure_agreeing_plus_equivocating :
  "\<forall> \<sigma> \<in> \<Sigma>. weight_measure (agreeing_validators (p, \<sigma>) \<union> equivocating_validators \<sigma>) = weight_measure (agreeing_validators (p, \<sigma>)) + equivocation_fault_weight \<sigma>"
  unfolding equivocation_fault_weight_def
  using agreeing_validators_are_not_equivocating weight_measure_disjoint_plus agreeing_validators_finite equivocating_validators_is_finite
  by simp

lemma (in Protocol) disagreeing_validators_weight_combined :
  "\<forall> \<sigma> \<in> \<Sigma>. weight_measure (disagreeing_validators (p, \<sigma>)) = weight_measure V - weight_measure (agreeing_validators (p, \<sigma>)) - equivocation_fault_weight \<sigma>"
  unfolding disagreeing_validators_def
  using weight_measure_agreeing_plus_equivocating
  unfolding equivocation_fault_weight_def
  using agreeing_validators_are_not_equivocating weight_measure_subset_minus agreeing_validators_finite equivocating_validators_is_finite
  by (smt Diff_empty Diff_iff Int_iff V_type agreeing_validators_type equivocating_validators_type finite_Diff old.prod.case subset_iff)

lemma (in Protocol) agreeing_validators_weight_combined :
  "\<forall> \<sigma> \<in> \<Sigma>. weight_measure (agreeing_validators (p, \<sigma>)) = weight_measure V - weight_measure (disagreeing_validators (p, \<sigma>)) - equivocation_fault_weight \<sigma>"
  using disagreeing_validators_weight_combined
  by simp

(* Definition 7.11 *)
definition (in Params) majority :: "(validator set * state) \<Rightarrow> bool"
  where
    "majority = (\<lambda>(v_set, \<sigma>). (weight_measure v_set > (weight_measure (V - equivocating_validators \<sigma>)) div 2))"
   
(* Definition 7.12 *)
definition (in Protocol) majority_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "majority_driven p = (\<forall> \<sigma> \<in> \<Sigma>. majority (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c))"

(* Definition 7.13 *)
definition (in Protocol) max_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "max_driven p =
      (\<forall> \<sigma> \<in> \<Sigma>. weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (disagreeing_validators (p, \<sigma>)) \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c))"

definition (in Protocol) max_driven_for_future :: "consensus_value_property \<Rightarrow> state \<Rightarrow> bool"
  where
    "max_driven_for_future p \<sigma> =
      (\<forall> \<sigma>' \<in> \<Sigma>. is_future_state (\<sigma>, \<sigma>') 
        \<longrightarrow> weight_measure (agreeing_validators (p, \<sigma>')) > weight_measure (disagreeing_validators (p, \<sigma>')) \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>'. p c))"

(* Definition 7.14 *)
definition later_disagreeing_messages :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_messages = (\<lambda>(p, m, v, \<sigma>).{m' \<in> later_from (m, v, \<sigma>). \<not> p (est m')})"

lemma (in Protocol) later_disagreeing_messages_type :
  "\<forall> p \<sigma> v m. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) \<subseteq> M"
  unfolding later_disagreeing_messages_def
  using later_from_type_for_state by auto

(* Definition 7.15 *)
(* NOTE: We use `the_elem` but is it return `undefined`?  *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)
(* NOTE: The original definition implies that validators in clique are not equivocating. 
         Here we explicitly states this. *)
definition is_clique :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique = (\<lambda>(v_set, p, \<sigma>). 
      (\<forall> v \<in> v_set. v \<in> observed_non_equivocating_validators \<sigma>  
       \<and> (\<forall> v' \<in> v_set. 
             agreeing (p, (the_elem (L_H_J \<sigma> v)), v')
             \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)))"

(* FIXME: We should prove that validators in clique see each other have a single latest message, 
          by the monotonicity of equivocations. The original definition implies it.  *)
lemma (in Protocol) non_equivocating_validator_is_non_equivocating_in_past :
  "\<forall> \<sigma> v \<sigma>'. v \<in> V \<and> {\<sigma>, \<sigma>'} \<subseteq> \<Sigma> \<and> is_future_state (\<sigma>', \<sigma>)
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>'"
  oops

lemma (in Protocol) validator_in_clique_see_L_H_M_of_others_is_singleton : 
  "\<forall> v_set p \<sigma>. v_set \<subseteq> V \<and> \<sigma> \<in> \<Sigma> 
  \<longrightarrow> is_clique (v_set, p, \<sigma>) 
  \<longrightarrow> (\<forall> v v'. {v, v'} \<subseteq> v_set \<longrightarrow> is_singleton (L_H_M (the_elem (L_H_J \<sigma> v)) v'))"
  sorry

(* ###################################################### *)
(* Section 7.3: Cliques Survive Messages from Validators Outside Clique *)
(* ###################################################### *)

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
lemma (in Protocol) L_M_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> L_H_M \<sigma> v = L_H_M \<sigma>' v"
  oops

(* Lemma 14 (Minimal transitions do not change latest justification for any non-sender). *)
lemma (in Protocol) latest_justificationss_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> L_H_J \<sigma> v = L_H_J \<sigma>' v"
  oops

(* Lemma 15 (Minimal transitions do not change Later Disagreeing for any non-sender). *)
lemma (in Protocol) later_disagreeing_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m \<in> M
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) = later_disagreeing_messages (p, m, v, \<sigma>')"
  oops


(* Lemma 16: Minimal transition from outside clique maintains clique *)
lemma (in Protocol) clique_not_affected_by_message_from_non_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> v_set
  \<longrightarrow> is_clique (v_set, p, \<sigma>) 
  \<longrightarrow> is_clique (v_set, p, \<sigma> \<union> {m})"
  sorry


(* ###################################################### *)
(* 7.4 Majority Cliques Survive Honest Messages from Validators in Clique *)
(* ###################################################### *)

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
  using strict_subset_of_state_have_immediately_next_messages
  apply (simp add: immediately_next_message_def)  
  oops

(* Lemma 19 (m' is its sender's latest message in \<sigma>’). *)
lemma (in Protocol) message_between_minimal_transition_is_latest_message :
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> m' = the_elem (L_H_M \<sigma>' v)"
  oops

(* Lemma 20 (Latest honest messages from non-equivocating messages are either the same as in their previous
latest message, or later) *)
lemma (in Protocol) latest_message_from_non_equivocating_validator_is_previous_latest_or_later:
  "\<forall> \<sigma> \<sigma>' m' v. (\<sigma>, \<sigma>') \<in> minimal_transitions
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma> \<and> v \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> the_elem (L_H_M (justification m') v) 
       = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m'))) v)
      \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m'))) v)) 
                  (the_elem (L_H_M (justification m') v))"
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
      \<and> (\<forall> v \<in> v_set. majority (v_set, the_elem (L_H_J \<sigma> v))) 
  \<longrightarrow> sender m' \<in> agreeing_validators (p, justification m')"
  oops


(* ###################################################### *)
(* 7.4.4 Honest messages from majority clique members do not break the clique *)
(* ###################################################### *)

(* Lemma 25 *)
lemma (in Protocol) latest_message_in_justification_of_new_message_is_latest_message :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> the_elem (L_H_M (justification m') (sender m')) = the_elem (L_H_M \<sigma> (sender m'))"
  oops

(* Lemma 26 *)
lemma (in Protocol) latest_message_justified_by_new_message :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> justified (the_elem (L_H_M \<sigma> (sender m'))) m'"
  oops

(* Lemma 27 (Nothing later than latest honest message).  *)
lemma (in Protocol) nothing_later_than_latest_honest_message :
  "\<forall> v \<sigma> m. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<and> m \<in> M
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> later_from (the_elem (L_H_M \<sigma> v), v, \<sigma>) =  \<emptyset>"
  oops

(* Lemma 28 (Later messages for sender is just the new message). *)
lemma (in Protocol) later_messages_for_sender_is_new_message :
  "\<forall> \<sigma> \<sigma>' m' v_set. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> v_set \<subseteq> V
  \<longrightarrow> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> sender m' \<notin> equivocating_validators \<sigma>'
  \<longrightarrow> later_from (the_elem (L_H_M \<sigma> (sender m')), sender m', \<sigma>') =  {m'}"
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
  \<longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m'))) v)), v, \<sigma>) = \<emptyset>
  \<longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (justification m') v)), v, \<sigma>) = \<emptyset>"
  oops

(* Lemma 31 (New non-equivocating latest messages from members of majority clique don’t break the clique) *)
lemma (in Protocol) clique_not_affected_by_honest_message_from_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> \<not> is_equivocating (\<sigma> \<union> {m}) (sender m)
  \<longrightarrow> is_clique (v_set, p, \<sigma>) 
  \<longrightarrow> is_clique (v_set, p, \<sigma> \<union> {m})"
  sorry

(* ###################################################### *)
(* 7.5 Equivocations from Validators in Clique do not break cliques *)
(* ###################################################### *)

(* Definition 7.18: One layer clique oracle threshold size *) 
definition (in Params) gt_threshold :: "(validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold 
       = (\<lambda>(v_set, \<sigma>).(weight_measure v_set > (weight_measure V) div 2 + t  - weight_measure (equivocating_validators \<sigma>)))"

(* Lemma 32 *)
lemma (in Protocol) gt_threshold_imps_majority_for_any_validator :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V
  \<longrightarrow> gt_threshold (v_set, \<sigma>) 
  \<longrightarrow> (\<forall> v \<in> v_set. majority (v_set, the_elem (L_H_J \<sigma> v)))"
  oops

(* Definition 7.19: Clique oracle with 1 layers *)
(* FIXME: Make the order of variables consistent to is_clique *)
(* Removed "- E(\<sigma>)" part from the original definition since it is included in is_clique *)
definition (in Params) is_clique_oracle :: "(validator set * state * consensus_value_property) \<Rightarrow> bool"
  where
    "is_clique_oracle 
       = (\<lambda>(v_set, \<sigma>, p). (is_clique (v_set, p, \<sigma>) \<and> gt_threshold (v_set, \<sigma>)))"

(* Lemma 33: Clique oracles preserved over message from non-member *)
lemma (in Protocol) clique_oracles_preserved_over_message_from_non_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> v_set
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma> \<union> {m}, p)"
  using clique_not_affected_by_message_from_non_member
  unfolding is_clique_oracle_def gt_threshold_def
  using equivocation_fault_weight_is_monotonic
  apply auto
  by (smt Un_insert_right \<Sigma>t_is_subset_of_\<Sigma> equivocation_fault_weight_def state_transition_by_immediately_next_message subsetCE subset_insertI sup_bot.right_neutral) 

(* Lemma 34: Clique oracles preserved over message from non-equivocating member *)
lemma (in Protocol) clique_oracles_preserved_over_message_from_non_equivocating_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> \<not> is_equivocating (\<sigma> \<union> {m}) (sender m)
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma> \<union> {m}, p)"
  using clique_not_affected_by_honest_message_from_member
  unfolding is_clique_oracle_def gt_threshold_def
  using equivocating_validators_preserved_over_honest_message
  using \<Sigma>t_is_subset_of_\<Sigma> by auto

(* Lemma 35: Clique oracles preserved over message from equivocating member *)
lemma (in Protocol) clique_oracles_preserved_over_message_from_equivocating_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> is_equivocating (\<sigma> \<union> {m}) (sender m)
  \<longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>t
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma> \<union> {m}, p)"
  (* using free_sub_clique *)
  sorry


(* NOTE: We will use this lemma instead of Lemma 36 *)
lemma (in Protocol) clique_oracles_preserved_over_immediately_next_message :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>t
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> is_clique_oracle (v_set, \<sigma> \<union> {m}, p)"
  using clique_oracles_preserved_over_message_from_non_member
        clique_oracles_preserved_over_message_from_non_equivocating_member
        clique_oracles_preserved_over_message_from_equivocating_member
  by (metis (no_types, lifting) Un_insert_right \<Sigma>t_def insert_subset mem_Collect_eq state_is_subset_of_M)

(* Lemma 37 *)
(* Based on no later disagreeing message imps keep agreeing  *)
lemma (in Protocol) clique_imps_everyone_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V 
  \<longrightarrow> is_clique (v_set, p, \<sigma>) 
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, \<sigma>)"
  apply (rule, rule, rule, rule, rule)
proof-
  fix \<sigma> v_set p assume "\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V"  and "is_clique (v_set, p, \<sigma>)" 
  then have clique: "\<forall> v \<in> v_set. v \<in> observed_non_equivocating_validators \<sigma>  
           \<and> later_disagreeing_messages (p,
                                         the_elem (L_H_M 
                                            (the_elem (L_H_J \<sigma> v)) v)
                                        , v, \<sigma>) = \<emptyset>"
    by (simp add: is_clique_def) 
  then have p_on_est : "\<forall> v \<in> v_set. (\<forall> m \<in> {m' \<in> \<sigma>. sender m' = v 
                                       \<and> justified (the_elem (L_H_M 
                                                          (the_elem (L_H_J \<sigma> v)) v))
                                                    m'}.
                                        p(est m))"
    by (simp add: later_disagreeing_messages_def later_from_def later_def from_sender_def)
  have "\<forall> v \<in> v_set. v \<in> observed_non_equivocating_validators \<sigma>" 
    using clique by simp
  then have "\<forall> v \<in> v_set. the_elem (L_H_J \<sigma> v)
                    =  justification (the_elem (L_H_M \<sigma> v))"
    apply (simp add: L_H_J_def)
    by (metis \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> empty_iff is_singleton_the_elem L_H_M_of_observed_non_equivocating_validator_is_singleton singletonD singletonI the_elem_image_unique)
  then have justified_ok: "\<forall> v \<in> v_set. justified (the_elem (L_H_M 
                                                          (the_elem (L_H_J \<sigma> v)) v))
                                    (the_elem (L_H_M \<sigma> v))"
    using validator_in_clique_see_L_H_M_of_others_is_singleton
    by (smt Diff_iff L_H_M_def L_H_M_is_in_the_state L_M_from_non_observed_validator_is_empty M_type \<open>\<forall>v\<in>v_set. v \<in> observed_non_equivocating_validators \<sigma>\<close> \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> \<open>is_clique (v_set, p, \<sigma>)\<close> empty_subsetI insert_subset is_singleton_the_elem justified_def observed_non_equivocating_validators_def state_is_subset_of_M subsetCE)
  have sender_ok: "\<forall> v \<in> v_set. sender (the_elem (L_H_M \<sigma> v)) = v" 
    using \<open>\<forall> v \<in> v_set. v \<in> observed_non_equivocating_validators \<sigma>\<close> sender_of_L_H_M
    using \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> by blast
  have "\<forall> v \<in> v_set.  the_elem (L_H_M \<sigma> v) \<in> \<sigma>"
    using \<open>\<forall> v \<in> v_set. v \<in> observed_non_equivocating_validators \<sigma>\<close> L_H_M_is_in_the_state
    using \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> by blast
  then have "\<forall> v \<in> v_set. p (est (the_elem (L_H_M \<sigma> v)))"
    using p_on_est sender_ok justified_ok
    by blast   
  then have "\<forall> v \<in> v_set. p (the_elem (L_H_E \<sigma> v))"
    apply (simp add: L_H_E_def)
    by (metis (no_types, lifting) \<open>\<forall>v\<in>v_set. v \<in> observed_non_equivocating_validators \<sigma>\<close> \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> empty_iff is_singleton_the_elem L_H_M_of_observed_non_equivocating_validator_is_singleton singletonD singletonI the_elem_image_unique)  
  then show "v_set \<subseteq> agreeing_validators (p, \<sigma>)"
    unfolding agreeing_validators_def agreeing_def
    by (smt \<open>\<forall>v\<in>v_set. v \<in> observed_non_equivocating_validators \<sigma>\<close> \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> is_singleton_the_elem mem_Collect_eq L_H_E_of_observed_non_equivocating_validator_is_singleton old.prod.case singletonD subsetI)
qed

(* Lemma 38 *)
lemma (in Protocol) threshold_sized_clique_imps_estimator_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> majority_driven p
  \<longrightarrow> is_clique (v_set - equivocating_validators \<sigma>, p, \<sigma>) \<and> gt_threshold (v_set - equivocating_validators \<sigma>, \<sigma>) 
  \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c)"
  apply (rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma> v_set p c
  assume  "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V"
  and "finite v_set"
  and "majority_driven p"
  and "is_clique (v_set - equivocating_validators \<sigma>, p, \<sigma>) \<and> gt_threshold (v_set - equivocating_validators \<sigma>, \<sigma>)"
  and "c \<in> \<epsilon> \<sigma>"
  then have "v_set - equivocating_validators \<sigma> \<subseteq> agreeing_validators (p, \<sigma>)" 
    using clique_imps_everyone_agreeing
    by (meson Diff_subset \<Sigma>t_is_subset_of_\<Sigma> subsetCE subset_trans)
  then have "weight_measure (v_set - equivocating_validators \<sigma>) \<le> weight_measure (agreeing_validators (p, \<sigma>))"
    using agreeing_validators_finite equivocating_validators_def weight_measure_subset_gte
          \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> \<open>finite v_set\<close>
    by (simp add: \<Sigma>t_def agreeing_validators_type)
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
      using weight_measure_subset_gte
      by (simp add: V_type)  
    then show ?thesis
      using \<open>weight_measure V / 2 < weight_measure (v_set - equivocating_validators \<sigma>)\<close> by linarith
  qed
  then have "weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (V - equivocating_validators \<sigma>) div 2" 
    using \<open>weight_measure (v_set - equivocating_validators \<sigma>) \<le> weight_measure (agreeing_validators (p, \<sigma>))\<close>
    by linarith  
  then show "p c"
    using \<open>majority_driven p\<close> unfolding majority_driven_def majority_def gt_threshold_def
    using \<open>c \<in> \<epsilon> \<sigma>\<close> 
    using Mi.simps \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> non_justifying_message_exists_in_M_0 by blast    
qed

(* Lemma 39: Cliques exist in all futures *)
lemma (in Protocol) clique_oracle_for_all_futures :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> \<sigma>' \<in> futures \<sigma>. is_clique_oracle (v_set, \<sigma>', p))"
  apply (rule+)
proof -
  fix \<sigma> v_set p \<sigma>'
  assume "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V" and "majority_driven p" and "is_clique_oracle (v_set, \<sigma>, p)" and "\<sigma>' \<in> futures \<sigma>" 
  show "is_clique_oracle (v_set, \<sigma>', p)"
    using clique_oracles_preserved_over_immediately_next_message
    (* TODO: Pick up immediately next message continuously to reach \<sigma>' *)
    sorry
qed

(* Lemma 40: Clique oracle is a safety oracle *)
lemma (in Protocol) clique_oracle_is_safety_oracle :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> majority_driven p
  \<longrightarrow> is_clique_oracle (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> \<sigma>' \<in> futures \<sigma>. naturally_corresponding_state_property p \<sigma>')"    
  using clique_oracle_for_all_futures threshold_sized_clique_imps_estimator_agreeing
  apply (simp add: is_clique_oracle_def naturally_corresponding_state_property_def)
  by (metis (mono_tags, lifting) futures_def mem_Collect_eq)
  
end