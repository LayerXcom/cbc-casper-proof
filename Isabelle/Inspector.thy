theory Inspector

imports Main CBCCasper LatestMessage StateTransition ConsensusSafety

begin

(* ###################################################### *)
(* Safety oracle (Inspector) *)
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
  by (simp add: agreeing_validators_def)

lemma (in Protocol) agreeing_validators_are_not_equivocating :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (p, \<sigma>) \<inter> equivocating_validators \<sigma> = \<emptyset>"
  using agreeing_validators_are_observed_non_equivocating_validators
        observed_non_equivocating_validators_are_not_equivocating 
  by blast

lemma (in Protocol) agreeing_validatros_subset_of_validators [simp]: "\<sigma> \<in> \<Sigma> \<Longrightarrow> agreeing_validators (p, \<sigma>) \<subseteq> V"
  apply (simp add: agreeing_validators_def observed_non_equivocating_validators_def observed_def)
  apply auto
  using M_type message_in_state_is_valid by blast

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
(* FIXME: Max driven and majority driven are equivalent. Keep one and discard the other. *)
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

lemma (in Protocol) non_equivocating_validator_is_non_equivocating_in_past :
  "\<forall> \<sigma> v \<sigma>'. v \<in> V \<and> {\<sigma>, \<sigma>'} \<subseteq> \<Sigma> \<and> is_future_state (\<sigma>', \<sigma>)
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>'"
  (* Will be proved by the monotonicity of equivocations. *)
  oops

(* Definition 7.18: Inspector threshold size *) 
(* FIXME: Use equivocation_fault_weight *)
definition (in Params) gt_threshold :: "(validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold 
       = (\<lambda>(v_set, \<sigma>).(weight_measure v_set > (weight_measure V) div 2 + t div 2 - equivocation_fault_weight \<sigma>))"

(* Lemma 32 *)
lemma (in Protocol) gt_threshold_imps_majority_for_agreeing_validator :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> agreeing_validators (p, \<sigma>)
  \<longrightarrow> gt_threshold (v_set, \<sigma>) 
  \<longrightarrow> (\<forall> v \<in> v_set. majority (v_set, the_elem (L_H_J \<sigma> v)))"
proof auto
  fix \<sigma> v_set v p
  assume "\<sigma> \<in> \<Sigma>t" "v_set \<subseteq> agreeing_validators (p, \<sigma>)" "gt_threshold (v_set, \<sigma>)" "v \<in> v_set"
  hence "weight_measure v_set > weight_measure V div 2 + t div 2 - equivocation_fault_weight \<sigma>"
    by (simp add: gt_threshold_def)
  hence "\<dots> > (weight_measure V - equivocation_fault_weight \<sigma>) div 2 + (t - equivocation_fault_weight \<sigma>) div 2"
    by (smt field_sum_of_halves)
  hence "\<dots> > (weight_measure V - equivocation_fault_weight \<sigma>) div 2"
    by (smt \<Sigma>t_def \<open>\<sigma> \<in> \<Sigma>t\<close> add.commute add.left_commute add_diff_cancel_left' add_diff_eq equivocation_fault_weight_def half_gt_zero_iff is_faults_lt_threshold_def mem_Collect_eq)
  hence "\<dots> > (weight_measure (agreeing_validators (p,\<sigma>)) + weight_measure (disagreeing_validators (p,\<sigma>))) div 2"
  proof-
    have "weight_measure V - equivocation_fault_weight \<sigma> = weight_measure (agreeing_validators (p,\<sigma>)) + weight_measure (disagreeing_validators (p,\<sigma>))"
      using agreeing_validators_weight_combined
      using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t\<close> by auto
    thus ?thesis
      using \<open>(weight_measure V - equivocation_fault_weight \<sigma>) / 2 < weight_measure v_set\<close> by auto
  qed
  hence "weight_measure (agreeing_validators (p,\<sigma>)) > (weight_measure (agreeing_validators (p,\<sigma>)) + weight_measure (disagreeing_validators (p,\<sigma>))) div 2"
  proof-
    have "weight_measure v_set \<le> weight_measure (agreeing_validators (p, \<sigma>))"
      using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t\<close> \<open>v_set \<subseteq> agreeing_validators (p, \<sigma>)\<close> weight_measure_subset_gte by auto
    thus ?thesis
      using \<open>(weight_measure (agreeing_validators (p, \<sigma>)) + weight_measure (disagreeing_validators (p, \<sigma>))) / 2 < weight_measure v_set\<close> by auto
  qed
  hence "weight_measure (agreeing_validators (p,\<sigma>)) > weight_measure (disagreeing_validators (p,\<sigma>))"
    by simp

  show "majority (v_set, the_elem (L_H_J \<sigma> v))"
    apply (simp add: majority_def)
    sorry
qed

definition (in Params) inspector :: "(validator set * state * consensus_value_property) \<Rightarrow> bool"
  where
    "inspector 
       = (\<lambda>(v_set, \<sigma>, p). v_set \<noteq> \<emptyset> \<and>
            (\<forall> v \<in> v_set. v \<in> agreeing_validators (p, \<sigma>)
              \<and> (\<exists> v_set'. v_set' \<subseteq> v_set \<and> gt_threshold(v_set', the_elem (L_H_J \<sigma> v)) 
                    \<and> (\<forall> v' \<in> v_set'. 
                        v' \<in> agreeing_validators (p, (the_elem (L_H_J \<sigma> v)))
                        \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))))"

definition (in Params) vinspector :: "state \<Rightarrow> consensus_value_property \<Rightarrow> bool" where
  "vinspector \<sigma> p \<equiv> (\<exists>v. inspector (v,\<sigma>,p))"

lemma (in Protocol) validator_in_inspector_see_L_H_M_of_others_is_singleton : 
  "\<forall> v_set p \<sigma>. v_set \<subseteq> V \<and> \<sigma> \<in> \<Sigma> 
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> v v'. {v, v'} \<subseteq> v_set \<longrightarrow> is_singleton (L_H_M (the_elem (L_H_J \<sigma> v)) v'))"
  oops

lemma (in Protocol) inspector_imps_everyone_observed_non_equivocating :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V 
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> v_set \<subseteq> observed_non_equivocating_validators (\<sigma>)"
  apply (simp add: inspector_def agreeing_validators_def)
  by blast

(* Lemma 37 *)
lemma (in Protocol) inspector_imps_everyone_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V 
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, \<sigma>)"
  apply (simp add: inspector_def)
  by blast

lemma (in Protocol) inspector_imps_gt_threshold :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V 
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> gt_threshold(v_set, \<sigma>)"
  apply (rule+)
proof - 
  fix \<sigma> v_set p
  assume "\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V"
  assume "inspector (v_set, \<sigma>, p)" 
  hence "\<exists> v \<in> v_set. \<exists> v_set'. v_set' \<subseteq> v_set \<and> gt_threshold(v_set', the_elem (L_H_J \<sigma> v))"
    apply (simp add: inspector_def)
    by blast
  hence "\<exists> v \<in> v_set.  gt_threshold(v_set, the_elem (L_H_J \<sigma> v))"
    apply (simp add: gt_threshold_def)
    using weight_measure_subset_gte
    by (smt \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close>) 
  obtain v where "v \<in> v_set \<and>  gt_threshold(v_set, the_elem (L_H_J \<sigma> v))"
    using \<open>\<exists>v\<in>v_set. gt_threshold (v_set, the_elem (L_H_J \<sigma> v))\<close> by blast
  hence "\<forall> \<sigma>' \<in> L_H_J \<sigma> v. \<sigma>' \<subseteq> \<sigma>"
    using L_H_J_is_subset_of_the_state \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close>
    by blast
  hence "is_singleton (L_H_J \<sigma> v) \<and> (\<forall> \<sigma>' \<in> L_H_J \<sigma> v. \<sigma>' \<subseteq> \<sigma>)"
    using L_H_J_is_subset_of_the_state \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> L_H_J_of_observed_non_equivocating_validator_is_singleton
          \<open>inspector (v_set, \<sigma>, p)\<close> 
    apply (simp add: inspector_def agreeing_validators_def)
    using \<open>v \<in> v_set \<and> gt_threshold (v_set, the_elem (L_H_J \<sigma> v))\<close> by auto  
  hence "the_elem (L_H_J \<sigma> v) \<subseteq> \<sigma>"
    by (metis insert_iff is_singleton_the_elem)
  then show "gt_threshold (v_set, \<sigma>)"
    using \<open>v \<in> v_set \<and> gt_threshold(v_set, the_elem (L_H_J \<sigma> v))\<close> 
    apply (simp add: gt_threshold_def)
    using equivocation_fault_weight_is_monotonic          
    apply (simp add: equivocation_fault_weight_def)
    by (smt L_H_J_type \<open>\<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V\<close> \<open>is_singleton (L_H_J \<sigma> v) \<and> (\<forall>\<sigma>'\<in>L_H_J \<sigma> v. \<sigma>' \<subseteq> \<sigma>)\<close> is_singleton_the_elem singletonI subsetCE) 
qed


lemma (in Protocol) gt_threshold_imps_estimator_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> majority_driven p
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, \<sigma>)
  \<longrightarrow> gt_threshold (v_set, \<sigma>) 
  \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c)"
  apply (rule, rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma> v_set p c
  assume "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V" "finite v_set" "majority_driven p"  "v_set \<subseteq> agreeing_validators (p, \<sigma>)" "gt_threshold (v_set, \<sigma>)" "c \<in> \<epsilon> \<sigma>"
  then have "weight_measure v_set \<le> weight_measure (agreeing_validators (p, \<sigma>))"
    using inspector_imps_everyone_agreeing
          weight_measure_subset_gte
          \<Sigma>t_is_subset_of_\<Sigma> agreeing_validators_type by auto
  then have "weight_measure v_set > (weight_measure V) div 2 + t div 2 - weight_measure (equivocating_validators \<sigma>)"
    using \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> \<open>gt_threshold (v_set, \<sigma>)\<close>
          gt_threshold_def
          equivocation_fault_weight_def
          \<Sigma>t_is_subset_of_\<Sigma> by auto
  then have "weight_measure v_set > (weight_measure V) div 2 - weight_measure (equivocating_validators \<sigma>) div 2"
    using  \<Sigma>t_def \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> equivocation_fault_weight_def is_faults_lt_threshold_def
    by auto
  then have "weight_measure v_set > (weight_measure (V - equivocating_validators \<sigma>)) div 2"
    by (metis Protocol.V_type Protocol_axioms \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> diff_divide_distrib equivocating_validators_is_finite equivocating_validators_type subsetCE weight_measure_subset_minus)
  then have "weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (V - equivocating_validators \<sigma>) div 2"
    using \<open>weight_measure v_set \<le> weight_measure (agreeing_validators (p, \<sigma>))\<close>
    by auto
  then show "p c"
    using \<open>majority_driven p\<close> unfolding majority_driven_def majority_def gt_threshold_def
    using \<open>c \<in> \<epsilon> \<sigma>\<close> Mi.simps \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> non_justifying_message_exists_in_M_0
    by blast
qed

(* Lemma 38 *)
lemma (in Protocol) inspector_imps_estimator_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> majority_driven p
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c)"
  by (simp add: gt_threshold_imps_estimator_agreeing inspector_imps_gt_threshold \<Sigma>t_def inspector_imps_everyone_agreeing)


(* ###################################################### *)
(* Section 7.3: Inspector Survive Messages from Non-member *)
(* ###################################################### *)

(* Lemma 11: Immediately next message does not change Later_From for any non-sender *)
lemma (in Protocol) later_from_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m m' v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> m' \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m')
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> later_from (m, v, \<sigma>) = later_from (m, v, \<sigma> \<union> {m'})"
  apply (simp add: later_from_def)
  by auto 

lemma (in Protocol) from_sender_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m m' v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> m' \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m')
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> from_sender (v, \<sigma>) = from_sender (v, \<sigma> \<union> {m'})"
  apply (simp add: from_sender_def)
  by auto 

(* Lemma 12: Immediately next message does not change equivocation status for any non-sender *)
lemma (in Protocol) equivocation_status_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> v \<in> V - {sender m}
  \<longrightarrow> v \<in> equivocating_validators \<sigma> \<longleftrightarrow> v \<in> equivocating_validators (\<sigma> \<union> {m})"
  apply (rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma> m v
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V"
  and "immediately_next_message (\<sigma>, m)"
  and "v \<in> V - {sender m}"
  then have g1: "observed \<sigma> \<subseteq> observed (\<sigma> \<union> {m})"
    apply (simp add: observed_def)
    by auto
  have g2: "is_equivocating \<sigma> v = is_equivocating (\<sigma> \<union> {m}) v"
    using \<open>v \<in> V - {sender m}\<close>
    apply (simp add: is_equivocating_def equivocation_def)
    by blast
  show "(v \<in> equivocating_validators \<sigma>) = (v \<in> equivocating_validators (\<sigma> \<union> {m}))"
    apply (simp add: equivocating_validators_def)
    using g1 g2
    by (metis (mono_tags, lifting) Un_insert_right is_equivocating_def mem_Collect_eq observed_def sup_bot.right_neutral)
qed

(* Lemma 13: Immediately next message does not change latest messages for any non-sender *)
lemma (in Protocol) L_H_M_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> v \<in> V - {sender m}
  \<longrightarrow> L_H_M \<sigma> v = L_H_M (\<sigma> \<union> {m}) v"
  apply (rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma> m v
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V" "immediately_next_message (\<sigma>, m)" "v \<in> V - {sender m}"
  show "L_H_M \<sigma> v = L_H_M (\<sigma> \<union> {m}) v"
  proof (cases "v \<in> equivocating_validators \<sigma>")
    case True
    then show ?thesis 
      apply (simp add: L_H_M_def)
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v \<in> V - {sender m}\<close> equivocation_status_of_non_sender_not_affected_by_minimal_transitions by auto 
  next
    case False
    then have "v \<notin> equivocating_validators \<sigma> \<and> v \<notin> equivocating_validators (\<sigma> \<union> {m})"
      using equivocation_status_of_non_sender_not_affected_by_minimal_transitions
            \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v \<in> V - {sender m}\<close> 
            by auto
    then show ?thesis
      apply (simp add: L_H_M_def L_M_def)
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v \<in> V - {sender m}\<close>
            later_from_of_non_sender_not_affected_by_minimal_transitions
            from_sender_of_non_sender_not_affected_by_minimal_transitions
      by (metis (no_types, lifting) Un_insert_right from_sender_type_for_state subsetCE sup_bot.right_neutral)       
  qed
qed    


lemma (in Protocol) agreeing_status_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m v p. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> v \<in> V - {sender m}
  \<longrightarrow> v \<in> agreeing_validators (p, \<sigma>) \<longleftrightarrow> v \<in> agreeing_validators (p, \<sigma> \<union> {m})"
  apply (simp add: agreeing_validators_def agreeing_def L_H_E_def observed_non_equivocating_validators_def observed_def)
  using L_H_M_of_non_sender_not_affected_by_minimal_transitions 
        equivocation_status_of_non_sender_not_affected_by_minimal_transitions
  by auto

(* Lemma 14 Immediately next message does not change latest justification for any non-sender *)
lemma (in Protocol) L_H_J_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> v \<in> V - {sender m}
  \<longrightarrow> L_H_J \<sigma> v = L_H_J (\<sigma> \<union> {m}) v"
  apply (simp add: L_H_J_def) 
  using L_H_M_of_non_sender_not_affected_by_minimal_transitions
  by auto 

(* Lemma 15 Immediately next message does not change Later Disagreeing for any non-sender *)
lemma (in Protocol) later_disagreeing_of_non_sender_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> m m' v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> m' \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m')
  \<longrightarrow> v \<in> V - {sender m'}
  \<longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) = later_disagreeing_messages (p, m, v, \<sigma> \<union> {m'})"
  apply (simp add: later_disagreeing_messages_def)
  using later_from_of_non_sender_not_affected_by_minimal_transitions by auto

(* Lemma 33: Inspector preserved over message from non-member *)
(* NOTE: Lemma 16 is not necessary *)
lemma (in Protocol) inspector_preserved_over_message_from_non_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> v_set
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)"
  apply (rule, rule, rule, rule, rule, rule, rule, rule)
proof - 
  fix \<sigma> m v_set p
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V" "immediately_next_message (\<sigma>, m)" "sender m \<notin> v_set" "inspector (v_set, \<sigma>, p)" 
  (* 1. agreeing_validators preserved *)
  then have "\<forall> v \<in> v_set. v \<in> agreeing_validators (p, \<sigma>) \<longrightarrow> v \<in> agreeing_validators (p, \<sigma> \<union> {m})"
    using agreeing_status_of_non_sender_not_affected_by_minimal_transitions
    by blast
  (* 2. gt_threshold preserved *)
  moreover have "\<forall> v \<in> v_set. 
                    (\<forall> v_set'. gt_threshold(v_set', the_elem (L_H_J \<sigma> v)) \<longrightarrow> gt_threshold(v_set', the_elem (L_H_J (\<sigma> \<union> {m}) v)))"
    using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> v_set\<close>
          L_H_J_of_non_sender_not_affected_by_minimal_transitions
    by fastforce
  (* 3. v_set' preserved *)
  moreover have "\<forall> v \<in> v_set.
                    (\<forall> v_set'. v_set' \<subseteq> v_set \<and>
                        (\<forall> v' \<in> v_set'. 
                            v' \<in> agreeing_validators (p, (the_elem (L_H_J \<sigma> v)))
                            \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)
                    \<longrightarrow> (\<forall> v' \<in> v_set'. 
                            v' \<in> agreeing_validators (p, (the_elem (L_H_J (\<sigma> \<union> {m}) v)))
                            \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"  
    apply (rule, rule, rule, rule)
  proof -
    fix v v_set' v'
    assume "v \<in> v_set" 
    and a1: "v_set' \<subseteq> v_set \<and> (\<forall> v' \<in> v_set'.
           v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)" 
    and "v' \<in> v_set'"
    then have l1: "v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>"
      by blast      
    have "v \<in> observed_non_equivocating_validators \<sigma>"
      using \<open>v \<in> v_set\<close> \<open>inspector (v_set, \<sigma>, p)\<close> inspector_imps_everyone_observed_non_equivocating
            \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> by blast 
    have "v' \<in> observed_non_equivocating_validators (the_elem (L_H_J \<sigma> v))"
      using l1 by (simp add: agreeing_validators_def)
    then have "v' \<in> V - {sender m}"
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>sender m \<notin> v_set\<close> \<open>v' \<in> v_set'\<close>
            a1 by blast 
    then moreover have "the_elem (L_H_J \<sigma> v) = the_elem (L_H_J (\<sigma> \<union> {m}) v)"
      using L_H_J_of_non_sender_not_affected_by_minimal_transitions \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> v_set\<close> \<open>v \<in> v_set\<close>
      by (metis (no_types, lifting) M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> insert_Diff insert_iff subsetCE)       
    then moreover have "the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v') = the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v')"
      using L_H_M_of_non_sender_not_affected_by_minimal_transitions
      by simp 
    then moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma> \<union> {m}) = \<emptyset>"
      proof -
        have ll1: "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma>)"
          by (simp add: calculation(2))
        have "\<sigma> \<union> {m} \<in> \<Sigma> \<and> v \<in> V"
          using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close>  state_transition_only_made_by_immediately_next_message
                \<open>v \<in> v_set\<close> by blast
        hence "the_elem (L_H_J (\<sigma> \<union> {m}) v) \<in> \<Sigma>"
          using L_H_J_type L_H_J_of_observed_non_equivocating_validator_is_singleton \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close>
          by (metis  \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> calculation(2) insert_subset is_singleton_the_elem) 
        hence "the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v') \<in> M"
          using L_H_M_type L_H_M_of_observed_non_equivocating_validator_is_singleton \<open>v' \<in> observed_non_equivocating_validators (the_elem (L_H_J \<sigma> v))\<close>
          using L_H_M_is_in_the_state calculation(2) state_is_subset_of_M by fastforce
        hence "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma>) = later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma> \<union> {m})"              
            using later_disagreeing_of_non_sender_not_affected_by_minimal_transitions ll1 
                  \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v' \<in> V - {sender m}\<close>
                  by auto
        then show ?thesis
          using l1 ll1 by blast  
        qed
    ultimately show "v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma> \<union> {m}) = \<emptyset>"
      using later_disagreeing_of_non_sender_not_affected_by_minimal_transitions l1
          \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v' \<in> V - {sender m}\<close>
      by simp         
  qed
  ultimately show "inspector (v_set, \<sigma> \<union> {m}, p)"
    using \<open>inspector (v_set, \<sigma>, p)\<close>
    apply (simp add: inspector_def)
    by meson
qed

(* ###################################################### *)
(* 7.4 Inspector Survives Honest Messages from Member *)
(* ###################################################### *)

(* TODO: This lemma must be redefined to consider threshold *)
(* 7.4.1 New messages at least leaves a smaller clique behind *)
(* Lemma 17: Free sub-clique *)
(* lemma (in Protocol) free_sub_clique :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> v_set
  \<longrightarrow> is_clique (v_set, p, \<sigma>) 
  \<longrightarrow> is_clique (v_set - {sender m}, p, \<sigma> \<union> {m})"
  oops
 *)

(* 7.4.2 Non-equivocating messages from member see all members agreeing *)
(* Lemma 18: Later messages from a non-equivocating validator include all earlier messages *)
(* NOTE: \<sigma>2 is not a state, just a set of messages. *)
lemma (in Protocol) later_messages_from_non_equivocating_validator_include_all_earlier_messages:
  assumes "v \<notin> equivocating_validators \<sigma>" "\<sigma>1 \<in> \<Sigma>" "\<sigma>1 \<subseteq> \<sigma>" "\<sigma>2 \<subseteq> \<sigma>" "\<sigma>1 \<inter> \<sigma>2 = \<emptyset>"
  shows "\<lbrakk> m1 \<in> \<sigma>1; sender m1 = v; m2 \<in> \<sigma>2; sender m2 = v \<rbrakk> \<Longrightarrow> m1 \<in> justification m2"
proof-
  have "v \<notin> equivocating_validators \<sigma>"
    using assms(1) by simp
  hence "v \<notin> {v'. v' \<in> V \<and> (\<exists>m1 \<in> \<sigma>. \<exists>m2 \<in> \<sigma>. sender m1 = v' \<and> equivocation (m1,m2))}"
    apply (auto simp add: equivocating_validators_def observed_def equivocation_def is_equivocating_def)
    by blast
  hence "\<And>m1 m2. m1 \<in> \<sigma> \<Longrightarrow> m2 \<in> \<sigma> \<Longrightarrow> \<not> equivocation (m1,m2) \<or> sender m1 \<noteq> v"
    using assms(1) equivocating_validators_def is_equivocating_def observed_def by force

  have "\<lbrakk> m1 \<in> \<sigma>; sender m1 = v; m2 \<in> \<sigma>; sender m2 = v \<rbrakk> \<Longrightarrow> \<not> equivocation (m1,m2)"
    using \<open>\<And>m2 m1. \<lbrakk>m1 \<in> \<sigma>; m2 \<in> \<sigma>\<rbrakk> \<Longrightarrow> \<not> equivocation (m1, m2) \<or> sender m1 \<noteq> v\<close> by blast
  hence "\<lbrakk> m1 \<in> \<sigma>1; sender m1 = v; m2 \<in> \<sigma>2; sender m2 = v \<rbrakk> \<Longrightarrow> \<not> equivocation (m1,m2)"
    using assms(3) assms(4) by blast
  {
    hence hyp: "\<lbrakk> m1 \<in> \<sigma>1; sender m1 = v; m2 \<in> \<sigma>2; sender m2 = v \<rbrakk> \<Longrightarrow> \<not> equivocation (m1,m2)" by simp
    assume "m1 \<in> \<sigma>1" "sender m1 = v" "m2 \<in> \<sigma>2" "sender m2 = v"
    hence "sender m1 \<noteq> sender m2 \<or> m1 = m2 \<or> m1 \<in> justification m2 \<or> m2 \<in> justification m1"
      using hyp
      by (simp add: equivocation_def justified_def)
    hence "m1 = m2 \<or> m1 \<in> justification m2 \<or> m2 \<in> justification m1"
      using \<open>sender m1 = v\<close> \<open>sender m2 = v\<close> by auto
    hence "m1 \<in> justification m2 \<or> m2 \<in> justification m1"
      using \<open>m1 \<in> \<sigma>1\<close> \<open>m2 \<in> \<sigma>2\<close> assms(5) by auto
    hence "m1 \<in> justification m2"
      by (metis Int_iff \<open>m1 \<in> \<sigma>1\<close> \<open>m2 \<in> \<sigma>2\<close> assms(2) assms(5) emptyE state_is_in_pow_Mi subset_eq)
  }
  thus "m1 \<in> \<sigma>1 \<Longrightarrow> sender m1 = v \<Longrightarrow> m2 \<in> \<sigma>2 \<Longrightarrow> sender m2 = v \<Longrightarrow> m1 \<in> justification m2" by simp
qed

(* Lemma 19: Immediately next message is it's sender's latest message in the next state *)
lemma (in Protocol) new_message_is_L_H_M_of_sender :
  "\<lbrakk> \<sigma> \<in> \<Sigma>; m \<in> M; immediately_next_message (\<sigma>, m); sender m \<notin> equivocating_validators (\<sigma> \<union> {m}) \<rbrakk>
  \<Longrightarrow> m = the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))"
  using L_H_M_of_observed_non_equivocating_validator_is_singleton
proof-
  assume "\<sigma> \<in> \<Sigma>" "m \<in> M" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})"
  have "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "\<sigma> \<inter> {m} = \<emptyset>"
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
    using \<open>immediately_next_message (\<sigma>, m)\<close> apply (simp add: immediately_next_message_def)
    done
  have "\<And>m1. \<lbrakk> m1 \<in> \<sigma>; sender m1 = sender m \<rbrakk> \<Longrightarrow> m1 \<in> justification m"
  proof-
    fix m1
    assume "m1 \<in> \<sigma>" "sender m1 = sender m"
    have "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "\<sigma> \<union> {m} \<in> \<Sigma>" "\<sigma> \<subseteq> \<sigma> \<union> {m}" "\<sigma> \<inter> {m} = \<emptyset>"
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
      using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> state_transition_only_made_by_immediately_next_message apply blast
      apply auto[1]
      by (simp add: \<open>\<sigma> \<inter> {m} = \<emptyset>\<close>)
    moreover have "m1 \<in> \<sigma>" "m \<in> {m}" "sender m1 = sender m"
      apply (simp add: \<open>m1 \<in> \<sigma>\<close>)
      apply simp
      by (simp add: \<open>sender m1 = sender m\<close>)
    ultimately show "m1 \<in> justification m"
      by (smt Un_subset_iff \<open>\<sigma> \<in> \<Sigma>\<close> later_messages_from_non_equivocating_validator_include_all_earlier_messages subset_iff_psubset_eq)
  qed
  hence "later_from (m, sender m, \<sigma>) = \<emptyset>"
    using equivocating_validators_implies_either_justified
    apply (simp add: later_from_def justified_def)
    apply auto
    by (meson \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> in_mono state_is_in_pow_Mi state_transition_only_made_by_immediately_next_message)
  hence "later_from (m, sender m, \<sigma> \<union> {m}) = \<emptyset>"
    apply (auto simp add: later_from_def justified_def)
    using \<open>m \<in> M\<close> justified_def message_cannot_justify_itself by blast
  hence "m \<in> L_H_M (\<sigma> \<union> {m}) (sender m)"
    apply (auto simp add: L_H_M_def L_M_def from_sender_def)
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
    done
  thus "m = the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))"
  proof-
    assume "m \<in> L_H_M (\<sigma> \<union> {m}) (sender m)"
    have "\<sigma> \<union> {m} \<in> \<Sigma>"
      using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> state_transition_only_made_by_immediately_next_message by blast
    moreover have "sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})"
      apply (auto simp add: observed_non_equivocating_validators_def observed_def)
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by auto
    ultimately have "is_singleton (L_H_M (\<sigma> \<union> {m}) (sender m))"
      using L_H_M_of_observed_non_equivocating_validator_is_singleton by blast
    show "m = the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))"
      by (metis \<open>is_singleton (L_H_M (\<sigma> \<union> {m}) (sender m))\<close> \<open>m \<in> L_H_M (\<sigma> \<union> {m}) (sender m)\<close> is_singleton_the_elem singletonD)
  qed
qed

lemma (in Protocol) new_justification_is_L_H_J_of_sender :
  "\<And>\<sigma> m v. \<lbrakk> \<sigma> \<in> \<Sigma>; m \<in> M; immediately_next_message (\<sigma>, m); sender m \<notin> equivocating_validators (\<sigma> \<union> {m}) \<rbrakk>
  \<Longrightarrow> the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m"
  using new_message_is_L_H_M_of_sender 
  apply (simp add: L_H_J_def) 
  using L_H_M_of_observed_non_equivocating_validator_is_singleton
  sorry

(* \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> *)

(* Lemma 20: Latest honest messages from non-equivocating messages are either the same as in their previous
latest message, or later *)
lemma (in Protocol) L_H_M_of_others_for_sender_is_the_previous_one_or_later:
  "\<forall> \<sigma> m v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>
  \<longrightarrow> the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)
        \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))"
  sorry

(* Lemma 21 *)
lemma (in Protocol) justified_message_exists_in_later_from:
  "\<forall> \<sigma> m1 m2. \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> \<sigma>
  \<longrightarrow> justified m1 m2 
  \<longrightarrow> m2 \<in> later_from (m1, sender m2, \<sigma>)"
  by (simp add: later_from_def later_def from_sender_def)

(* Lemma 22. *)

(* Lemma 23: Non-equivocating messages from member see all members agreeing *)
lemma (in Protocol) new_message_see_all_members_agreeing :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, justification m)"
  sorry


(* 7.4.3 Non-equivocating messages from member agree *)

(* Lemma 24: New messages from member is agreeing *)
lemma (in Protocol) new_message_from_member_see_itself_agreeing :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> sender m \<in> agreeing_validators (p, justification m)"
  using new_message_see_all_members_agreeing
  by blast 

(* 7.4.4 Honest messages from member do not break inspector *)

(* Lemma 25 *)
lemma (in Protocol) L_H_M_of_sender_is_previous_L_H_M :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> M 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> the_elem (L_H_M (justification m) (sender m)) = the_elem (L_H_M \<sigma> (sender m))"
  sorry


(* Lemma 26 *)
lemma (in Protocol) L_H_M_of_sender_justified_by_new_message :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> M 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> justified (the_elem (L_H_M \<sigma> (sender m))) m"
  (* Proved by the totalitiy of justification and the fact that m \<notin> justification L_H_M() *)
  using justification_is_total_on_messages_from_non_equivocating_validator
  sorry

(* Lemma 27: Nothing later than latest honest message *)
lemma (in Protocol) nothing_later_than_L_H_M :
  "\<forall> \<sigma> m v. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V
  \<longrightarrow> v \<notin> equivocating_validators \<sigma>
  \<longrightarrow> later_from (the_elem (L_H_M \<sigma> v), v, \<sigma>) = \<emptyset>"
  apply (simp add: later_from_def L_H_M_def L_M_def from_sender_def justified_def equivocating_validators_def is_equivocating_def) 
  sorry

(* Lemma 28: Later messages for sender is just the new message *)
lemma (in Protocol) later_messages_for_sender_is_only_new_message :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> M 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma> \<union> {m}) =  {m}"
  sorry

(* Lemma 29: Later disagreeing is monotonic *)
lemma (in Protocol) later_disagreeing_is_monotonic:
  "\<forall> v \<sigma> m1 m2 p. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> M
  \<longrightarrow> justified m1 m2
  \<longrightarrow> later_disagreeing_messages (p, m2, v, \<sigma>) \<subseteq> later_disagreeing_messages (p, m1, v, \<sigma>)"
  using message_in_state_is_strict_subset_of_the_state message_in_state_is_valid M_type state_is_in_pow_Mi  
  apply (simp add: later_disagreeing_messages_def later_from_def justified_def)
  by auto

(* Lemma 30 *)
lemma (in Protocol) previous_empty_later_disagreeing_messages_imps_empty_in_new_message :
  "\<forall> \<sigma> m v p. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)), v, \<sigma>) = \<emptyset>
  \<longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (justification m) v)), v, \<sigma>) = \<emptyset>"
  apply (simp add: later_disagreeing_messages_def)
  sorry

(* Lemma 34: Inspector preserved over message from non-equivocating member *)
(* NOTE: Lemma 31 is not necessary*)
lemma (in Protocol) inspector_preserved_over_message_from_non_equivocating_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)"
  apply (rule+)
proof - 
  fix \<sigma> m v_set p
  assume "\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V" "finite v_set" "majority_driven p" "immediately_next_message (\<sigma>, m)" "sender m \<in> v_set" 
        "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "inspector (v_set, \<sigma>, p)" 
  (* Useful lemmas *)
  then have "\<sigma> \<union> {m} \<in> \<Sigma>t"
    by (metis (no_types, lifting) \<Sigma>t_def equivocating_validators_preserved_over_honest_message equivocation_fault_weight_def is_faults_lt_threshold_def mem_Collect_eq state_transition_by_immediately_next_message)    
  then have "sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})"
    using inspector_imps_everyone_observed_non_equivocating \<open>inspector (v_set, \<sigma>, p)\<close> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close>
    apply (simp add: observed_non_equivocating_validators_def observed_def)
    by blast    
  then have "the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m"
    using new_justification_is_L_H_J_of_sender
          \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close>
    by (simp add: \<Sigma>t_def)  
  (* 1. gt_threshold preserved *)
  then moreover have "\<forall> v \<in> v_set.
                    (\<forall> v_set'.  v_set' \<subseteq> v_set \<and> gt_threshold(v_set', the_elem (L_H_J \<sigma> v)) \<longrightarrow> gt_threshold(v_set', the_elem (L_H_J (\<sigma> \<union> {m}) v)))"
    using \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<in> v_set\<close>
          L_H_J_of_non_sender_not_affected_by_minimal_transitions
    sorry
  (* 2. agreeing_validators preserved *)
  then moreover have "\<forall> v \<in> v_set. v \<in> agreeing_validators (p, \<sigma> \<union> {m})"
  proof -
    have "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})"
    proof -
      have "\<forall> v_set'. v_set' \<subseteq> v_set \<longrightarrow> v_set' \<subseteq> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)))"  
        using new_message_see_all_members_agreeing
        by (smt Protocol.new_message_see_all_members_agreeing Protocol_axioms \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> \<open>the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m\<close> subsetCE subset_trans) 
      have "\<exists> v_set'. v_set' \<subseteq> v_set \<and> gt_threshold(v_set', the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)))"
        using \<open>inspector (v_set, \<sigma>, p)\<close>
        apply (simp add: inspector_def)
        using \<open>\<forall>v\<in>v_set. \<forall>v_set'.  v_set' \<subseteq> v_set \<and> gt_threshold (v_set', the_elem (L_H_J \<sigma> v)) \<longrightarrow> gt_threshold (v_set', the_elem (L_H_J (\<sigma> \<union> {m}) v))\<close>
                \<open>sender m \<in> v_set\<close>  \<open>the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m\<close>
        by (smt Un_insert_right \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> subsetCE subset_trans sup_bot.right_neutral)        
      then have "\<exists> v_set'. v_set' \<subseteq> V \<and> finite v_set' 
                \<and> v_set' \<subseteq> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and> gt_threshold(v_set', the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)))"
        using \<open>finite v_set\<close> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>\<forall> v_set'. v_set' \<subseteq> v_set \<longrightarrow> v_set' \<subseteq> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)))\<close>
        by (meson rev_finite_subset subset_trans) 
      then have "\<forall> c \<in> \<epsilon> (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))). p c"
        using  \<open>majority_driven p\<close> \<open>sender m \<in> v_set\<close> gt_threshold_imps_estimator_agreeing \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close>
              \<open>sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})\<close> \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> \<open>the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m\<close>        
              past_state_of_\<Sigma>t_is_\<Sigma>t state_transition_is_immediately_next_message M_type
        unfolding \<Sigma>t_def
        by (smt \<Sigma>t_def \<Sigma>t_is_subset_of_\<Sigma> is_future_state.simps subsetD)
      then have "\<forall> c \<in> L_H_E (\<sigma> \<union> {m}) (sender m). p c"
        using \<open>sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})\<close> \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> L_H_M_of_observed_non_equivocating_validator_is_singleton
        apply (simp add: L_H_E_def L_H_J_def)      
        sorry
      then show ?thesis  
        using \<open>sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})\<close>
        by (simp add: agreeing_validators_def agreeing_def)       
    qed
    then show ?thesis
      using agreeing_status_of_non_sender_not_affected_by_minimal_transitions
      by (smt Diff_iff \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>inspector (v_set, \<sigma>, p)\<close> contra_subsetD empty_iff insert_iff inspector_imps_everyone_agreeing)
  qed      
  (* 3. v_set' preserved *)
  moreover have "\<forall> v \<in> v_set.
                    (\<forall> v_set'. v_set' \<subseteq> v_set \<and>
                        (\<forall> v' \<in> v_set'. 
                            v' \<in> agreeing_validators (p, (the_elem (L_H_J \<sigma> v)))
                            \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)
                    \<longrightarrow> (\<forall> v' \<in> v_set'. 
                            v' \<in> agreeing_validators (p, (the_elem (L_H_J (\<sigma> \<union> {m}) v)))
                            \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"  
    apply (rule, rule, rule, rule)
  proof -
    fix v v_set' v'
    assume "v \<in> v_set" 
    and a1: "v_set' \<subseteq> v_set \<and> (\<forall> v' \<in> v_set'.
           v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)" 
    and "v' \<in> v_set'"
    show "v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma> \<union> {m}) = \<emptyset>"
      sorry
    qed
  ultimately show "inspector (v_set, \<sigma> \<union> {m}, p)"
    using \<open>inspector (v_set, \<sigma>, p)\<close>
    apply (simp add: inspector_def)
    by meson
qed

lemma (in Protocol)
  "\<forall> \<sigma> m p. \<sigma> \<in> \<Sigma>t \<and> m \<in> M
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> vinspector \<sigma> p 
  \<longrightarrow> vinspector (\<sigma> \<union> {m}) p"
  apply rule+
proof-
  fix \<sigma> m p v
  assume "\<sigma> \<in> \<Sigma>t \<and> m \<in> M" "majority_driven p" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "vinspector \<sigma> p"

  obtain v_set where insp: "inspector (v_set, \<sigma>, p)"
    using vinspector_def
    using \<open>vinspector \<sigma> p\<close> by blast

  have "v_set \<noteq> \<emptyset> \<and> v_set \<subseteq> agreeing_validators (p, \<sigma>)"
    using insp
    apply (simp add: inspector_def, auto)
    done

  have "the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m"
    using new_justification_is_L_H_J_of_sender
    sorry

  show "vinspector (\<sigma> \<union> {m}) p"
    apply (simp add: vinspector_def inspector_def)
    sorry
qed

(* ###################################################### *)
(* 7.5 Equivocations from member do not break inspector *)
(* ###################################################### *)

(* Lemma 35: Inspector preserved over message from equivocating member *)
lemma (in Protocol) inspector_preserved_over_message_from_equivocating_member :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> sender m \<in> v_set
  \<longrightarrow> sender m \<in> equivocating_validators (\<sigma> \<union> {m})
  \<longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>t
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)"
  (* Since \<sigma> \<union> {m} \<in> \<Sigma>t, gt_threshold still holds  *)
  sorry


(* Lemma 36 *)
lemma (in Protocol) inspector_preserved_over_immediately_next_message :
  "\<forall> \<sigma> m v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> immediately_next_message (\<sigma>, m)
  \<longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>t
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)"
  using inspector_preserved_over_message_from_non_member
        inspector_preserved_over_message_from_non_equivocating_member
        inspector_preserved_over_message_from_equivocating_member
  apply (simp add: \<Sigma>t_def)
  by (metis V_type insert_iff message_in_state_is_valid rev_finite_subset)


(* Lemma 39: Inspector exists in all future states *)
lemma (in Protocol) inspector_preserved_in_future:
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> majority_driven p
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> (\<forall> \<sigma>' \<in> futures \<sigma>. inspector (v_set, \<sigma>', p))"
proof auto
  fix \<sigma> v_set p \<sigma>'
  assume "\<sigma> \<in> \<Sigma>t" "v_set \<subseteq> V" "majority_driven p" "inspector (v_set, \<sigma>, p)" "\<sigma>' \<in> futures \<sigma>"
  hence "\<sigma> \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>"
    unfolding \<Sigma>t_def futures_def
    by auto

  have "\<sigma>' \<in> \<Sigma>t"
    using \<open>\<sigma>' \<in> futures \<sigma>\<close> futures_def by blast

  obtain message_list where "MessagePath \<sigma> \<sigma>' message_list"
    using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> futures \<sigma>\<close> exist_message_path by blast

  have "\<lbrakk> MessagePath \<sigma> \<sigma>' message_list; \<sigma> \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>t; inspector (v_set, \<sigma>, p) \<rbrakk> \<Longrightarrow> inspector (v_set, \<sigma>', p)"
    apply (induct "length message_list" arbitrary: message_list \<sigma> \<sigma>')
    apply (simp)
    using coherent_nil_message_path apply auto[1]
  proof-
    fix n message_list \<sigma> \<sigma>'
    assume "\<And>message_list \<sigma> \<sigma>'.
           n = length message_list \<Longrightarrow> MessagePath \<sigma> \<sigma>' message_list \<Longrightarrow> \<sigma> \<in> \<Sigma> \<Longrightarrow> \<sigma>' \<in> \<Sigma> \<Longrightarrow> \<sigma>' \<in> \<Sigma>t \<Longrightarrow> inspector (v_set, \<sigma>, p) \<Longrightarrow> inspector (v_set, \<sigma>', p)"
    and "Suc n = length message_list" "MessagePath \<sigma> \<sigma>' message_list" "\<sigma> \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>t" "inspector (v_set, \<sigma>, p)"

    obtain m ms where "message_list = m # ms" "MessagePath (\<sigma> \<union> {m}) \<sigma>' ms" "immediately_next_message (\<sigma>,m)" "\<sigma> \<union> {m} \<in> \<Sigma>"
      by (metis \<open>MessagePath \<sigma> \<sigma>' message_list\<close> \<open>Suc n = length message_list\<close> coherent_nonnil_message_path nat.distinct(1))
    hence "\<sigma> \<in> \<Sigma>t" "\<sigma> \<union> {m} \<in> \<Sigma>t"
      apply (meson \<open>MessagePath \<sigma> \<sigma>' message_list\<close> \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> coherent_message_path_inclusive is_future_state.simps past_state_of_\<Sigma>t_is_\<Sigma>t)
      apply (meson \<open>MessagePath (\<sigma> \<union> {m}) \<sigma>' ms\<close> \<open>\<sigma> \<union> {m} \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> coherent_message_path_inclusive is_future_state.simps past_state_of_\<Sigma>t_is_\<Sigma>t)
      done
    have "inspector (v_set, \<sigma> \<union> {m}, p)"
      using \<open>\<sigma> \<in> \<Sigma>t\<close> \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>majority_driven p\<close> \<open>v_set \<subseteq> V\<close> inspector_preserved_over_immediately_next_message by blast
    moreover have "n = length ms"
      using \<open>Suc n = length message_list\<close> \<open>message_list = m # ms\<close> by auto
    moreover have "MessagePath (\<sigma> \<union> {m}) \<sigma>' ms"
      using \<open>MessagePath (\<sigma> \<union> {m}) \<sigma>' ms\<close> by auto
    moreover have "\<sigma> \<union> {m} \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>"
      using \<open>\<sigma> \<union> {m} \<in> \<Sigma>\<close> apply auto[1]
      by (simp add: \<open>\<sigma>' \<in> \<Sigma>\<close>)
    moreover have "\<sigma> \<union> {m} \<in> \<Sigma>t"
      using \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> by auto
    ultimately show "inspector (v_set, \<sigma>', p)"
      using \<open>\<And>message_list \<sigma>' \<sigma>. \<lbrakk>n = length message_list; MessagePath \<sigma> \<sigma>' message_list; \<sigma> \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>t; inspector (v_set, \<sigma>, p)\<rbrakk> \<Longrightarrow> inspector (v_set, \<sigma>', p)\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> by blast
  qed
  
  thus "inspector (v_set, \<sigma>', p)"
    using \<open>MessagePath \<sigma> \<sigma>' message_list\<close> \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> \<open>inspector (v_set, \<sigma>, p)\<close> by blast
qed


(* Lemma 40: Inspector is a safety oracle *)
lemma (in Protocol) inspector_is_safety_oracle :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<longrightarrow> finite v_set
  \<longrightarrow> majority_driven p
  \<longrightarrow> inspector (v_set, \<sigma>, p)
  \<longrightarrow> state_property_is_decided (naturally_corresponding_state_property p, \<sigma>)"    
  using inspector_preserved_in_future inspector_imps_estimator_agreeing
  apply (simp add: naturally_corresponding_state_property_def futures_def state_property_is_decided_def)
  by meson

end