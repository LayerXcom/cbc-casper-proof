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
  apply (simp add: agreeing_validators_def)
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

lemma (in Protocol) agreeing_validatros_subset_of_validators [simp]: "\<sigma> \<in> \<Sigma> \<Longrightarrow> agreeing_validators (p, \<sigma>) \<subseteq> V"
  apply (simp add: agreeing_validators_def observed_def)
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
  apply (simp add: disagreeing_validators_def agreeing_validators_def agreeing_def)
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
  "\<lbrakk> v \<in> V; {\<sigma>, \<sigma>'} \<subseteq> \<Sigma>; is_future_state (\<sigma>, \<sigma>'); v \<notin> equivocating_validators \<sigma>' \<rbrakk> \<Longrightarrow> v \<notin> equivocating_validators \<sigma>"
proof-
  assume "v \<in> V" "{\<sigma>, \<sigma>'} \<subseteq> \<Sigma>" "is_future_state (\<sigma>, \<sigma>')" "v \<notin> equivocating_validators \<sigma>'"
  have "v \<in> equivocating_validators \<sigma> \<Longrightarrow> v \<in> equivocating_validators \<sigma>'"
    using \<open>is_future_state (\<sigma>, \<sigma>')\<close> \<open>v \<in> V\<close> equivocation_is_monotonic by blast
  show "v \<notin> equivocating_validators \<sigma>"
    using \<open>v \<in> equivocating_validators \<sigma> \<Longrightarrow> v \<in> equivocating_validators \<sigma>'\<close> \<open>v \<notin> equivocating_validators \<sigma>'\<close> by blast
qed

(* Definition 7.18: Inspector threshold size *) 
definition (in Params) gt_threshold :: "(validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold 
       = (\<lambda>(v_set, \<sigma>).(weight_measure v_set > (weight_measure V) div 2 + t - equivocation_fault_weight \<sigma>))"

(* Lemma 32 *)
lemma (in Protocol) gt_threshold_imps_majority_for_agreeing_validator :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> agreeing_validators (p, \<sigma>)
  \<longrightarrow> gt_threshold (v_set, \<sigma>) 
  \<longrightarrow> (\<forall> v \<in> v_set. majority (v_set, the_elem (L_H_J \<sigma> v)))"
proof auto
  fix \<sigma> v_set v p
  assume "\<sigma> \<in> \<Sigma>t" "v_set \<subseteq> agreeing_validators (p, \<sigma>)" "gt_threshold (v_set, \<sigma>)" "v \<in> v_set"
  have "\<sigma> \<in> \<Sigma>"
    using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t\<close> by blast
  have "the_elem (L_H_J \<sigma> v) \<in> \<Sigma>"
    apply (rule L_H_J_is_state_if_exists)
    using \<open>\<sigma> \<in> \<Sigma>\<close> apply blast
    using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>v \<in> v_set\<close> \<open>v_set \<subseteq> agreeing_validators (p, \<sigma>)\<close> agreeing_validators_are_observed_non_equivocating_validators by blast

  have "weight_measure v_set > weight_measure V div 2 + t - equivocation_fault_weight \<sigma>"
    using \<open>gt_threshold (v_set, \<sigma>)\<close>
    by (simp add: gt_threshold_def)
  also have "\<dots> > weight_measure V div 2"
  proof-
    have "equivocation_fault_weight \<sigma> < t"
      using \<open>\<sigma> \<in> \<Sigma>t\<close>
      apply (simp add: \<Sigma>t_def is_faults_lt_threshold_def)
      done
    thus ?thesis
      using calculation
      by linarith
  qed
  moreover have "weight_measure V \<ge> weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> v)))"
  proof-
    have x: "weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> v))) = weight_measure V - weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> v)))"
      apply (rule weight_measure_subset_minus [symmetric])
      using \<open>the_elem (L_H_J \<sigma> v) \<in> \<Sigma>\<close> equivocating_validators_is_finite apply blast
      apply (simp add: V_type)
      by (simp add: \<open>the_elem (L_H_J \<sigma> v) \<in> \<Sigma>\<close>)
    show ?thesis
      apply (simp add: x)
      by (simp add: \<open>the_elem (L_H_J \<sigma> v) \<in> \<Sigma>\<close> weight_positive)
  qed
  ultimately have "weight_measure v_set > weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> v))) div 2"
    by linarith
  thus "majority (v_set, the_elem (L_H_J \<sigma> v))"
    apply (simp add: majority_def)
    done
qed

definition (in Params) inspector :: "(validator set * state * consensus_value_property) \<Rightarrow> bool"
  where
    "inspector 
       = (\<lambda>(v_set, \<sigma>, p). v_set \<noteq> \<emptyset> \<and> v_set \<subseteq> V \<and>
            (\<forall> v \<in> v_set. v \<in> agreeing_validators (p, \<sigma>)
              \<and> (\<exists> v_set'. v_set' \<subseteq> v_set \<and> gt_threshold(v_set', \<sigma>) 
                    \<and> (\<forall> v' \<in> v_set'. 
                        v' \<in> agreeing_validators (p, (the_elem (L_H_J \<sigma> v)))
                        \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))))"

definition (in Params) vinspector :: "state \<Rightarrow> consensus_value_property \<Rightarrow> bool" where
  "vinspector \<sigma> p \<equiv> (\<exists>v \<subseteq> V. inspector (v,\<sigma>,p))"

definition (in Params) vinspector_with :: "state \<Rightarrow> consensus_value_property \<Rightarrow> (validator set \<Rightarrow> bool) \<Rightarrow> bool" where
  "vinspector_with \<sigma> p Q \<equiv> (\<exists>v_set. inspector (v_set,\<sigma>,p) \<and> Q v_set)"

lemma (in Protocol) inspector_imps_belonging_validator_is_agreeing:
  "\<lbrakk> inspector (v_set, \<sigma>, p); v \<in> v_set \<rbrakk> \<Longrightarrow> v \<in> agreeing_validators (p, \<sigma>)"
  apply (simp add: inspector_def)
  done

lemma (in Protocol) inspector_imps_everyone_observed_non_equivocating :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma> 
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> v_set \<subseteq> observed_non_equivocating_validators (\<sigma>)"
  apply (simp add: inspector_def agreeing_validators_def)
  by blast

(* Lemma 37 *)
lemma (in Protocol) inspector_imps_everyone_agreeing :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> v_set \<subseteq> agreeing_validators (p, \<sigma>)"
  apply (simp add: inspector_def)
  by blast

lemma (in Protocol) inspector_imps_gt_threshold :
  "\<forall> \<sigma> v_set p. \<sigma> \<in> \<Sigma>
  \<longrightarrow> inspector (v_set, \<sigma>, p) 
  \<longrightarrow> gt_threshold(v_set, \<sigma>)"
  apply (rule+)
proof - 
  fix \<sigma> v_set p
  assume "\<sigma> \<in> \<Sigma>"
  assume "inspector (v_set, \<sigma>, p)"
  hence "v_set \<subseteq> V"
    by (simp add: inspector_def)

  have "\<exists> v \<in> v_set. \<exists> v_set'. v_set' \<subseteq> v_set \<and> gt_threshold(v_set', \<sigma>)"
    using \<open>inspector (v_set, \<sigma>, p)\<close>
    apply (simp add: inspector_def)
    by blast
  hence "\<exists> v \<in> v_set.  gt_threshold(v_set, \<sigma>)"
    apply (simp add: gt_threshold_def)
    using weight_measure_subset_gte
    by (smt \<open>v_set \<subseteq> V\<close>)
  obtain v where "v \<in> v_set \<and>  gt_threshold(v_set, \<sigma>)"
    using \<open>\<exists>v\<in>v_set. gt_threshold (v_set, \<sigma>)\<close> by blast
  then show "gt_threshold (v_set, \<sigma>)"
    using \<open>v \<in> v_set \<and> gt_threshold(v_set, \<sigma>)\<close> 
    apply (simp add: gt_threshold_def)
    done
qed


lemma (in Protocol) gt_threshold_imps_estimator_agreeing :
  "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<Longrightarrow> finite v_set
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> v_set \<subseteq> agreeing_validators (p, \<sigma>)
  \<Longrightarrow> gt_threshold (v_set, \<sigma>) 
  \<Longrightarrow> (\<And>c. c \<in> \<epsilon> \<sigma> \<Longrightarrow> p c)"
proof-
  fix \<sigma> v_set p c
  assume "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V" "finite v_set" "majority_driven p"  "v_set \<subseteq> agreeing_validators (p, \<sigma>)" "gt_threshold (v_set, \<sigma>)" "c \<in> \<epsilon> \<sigma>"

  have "t > equivocation_fault_weight \<sigma>"
    using Params.is_faults_lt_threshold_def \<Sigma>t_def \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> by blast

  have "weight_measure v_set > weight_measure V div 2 + t - equivocation_fault_weight \<sigma>"
    using \<open>gt_threshold (v_set, \<sigma>)\<close>
    by (simp add: gt_threshold_def)
  moreover have "weight_measure V div 2 + t - equivocation_fault_weight \<sigma> > weight_measure (V - equivocating_validators \<sigma>) div 2"
  proof auto
    have "weight_measure (V - equivocating_validators \<sigma>) = weight_measure V - weight_measure (equivocating_validators \<sigma>)"
      using V_type \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> equivocating_validators_is_finite weight_measure_subset_minus by auto
    moreover have "t * 2 > equivocation_fault_weight \<sigma>"
      using Protocol.t_type(1) Protocol_axioms \<open>equivocation_fault_weight \<sigma> < t\<close> by fastforce
    ultimately show "weight_measure (V - equivocating_validators \<sigma>) < weight_measure V + t * 2 - equivocation_fault_weight \<sigma> * 2"
      by (simp add: equivocation_fault_weight_def)
  qed
  ultimately have "weight_measure v_set > weight_measure (V - equivocating_validators \<sigma>) div 2"
    by simp
  hence "weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (V - equivocating_validators \<sigma>) div 2"
  proof-
    assume "weight_measure (V - equivocating_validators \<sigma>) / 2 < weight_measure v_set"

    have "weight_measure (agreeing_validators (p, \<sigma>)) \<ge> weight_measure v_set"
      using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> \<open>v_set \<subseteq> agreeing_validators (p, \<sigma>)\<close> weight_measure_subset_gte by auto
    thus ?thesis
      using \<open>weight_measure (V - equivocating_validators \<sigma>) / 2 < weight_measure v_set\<close> by linarith
  qed
  then show "p c"
    using \<open>majority_driven p\<close> unfolding majority_driven_def majority_def gt_threshold_def
    using \<open>c \<in> \<epsilon> \<sigma>\<close> Mi.simps \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V\<close> non_justifying_message_exists_in_M_0
    by blast
qed

(* Lemma 38 *)
lemma (in Protocol) inspector_imps_estimator_agreeing :
  "\<sigma> \<in> \<Sigma>t \<and> v_set \<subseteq> V 
  \<Longrightarrow> finite v_set
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> inspector (v_set, \<sigma>, p) 
  \<Longrightarrow> (\<And>c. c \<in> \<epsilon> \<sigma> \<Longrightarrow> p c)"
  by (simp add: gt_threshold_imps_estimator_agreeing inspector_imps_gt_threshold \<Sigma>t_def inspector_imps_everyone_agreeing)

lemma (in Protocol) vinspector_imps_estimator_agreeing :
  "\<sigma> \<in> \<Sigma>t
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> vinspector \<sigma> p 
  \<Longrightarrow> (\<And>c. c \<in> \<epsilon> \<sigma> \<Longrightarrow> p c)"
  using inspector_imps_estimator_agreeing vinspector_def
  by (meson V_type rev_finite_subset)

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
  apply (simp add: agreeing_validators_def agreeing_def L_H_E_def observed_def)
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
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> m' \<in> M \<and> v \<in> V 
  \<Longrightarrow> immediately_next_message (\<sigma>, m')
  \<Longrightarrow> v \<in> V - {sender m'}
  \<Longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) = later_disagreeing_messages (p, m, v, \<sigma> \<union> {m'})"
  apply (simp add: later_disagreeing_messages_def)
  using later_from_of_non_sender_not_affected_by_minimal_transitions by auto

(* Lemma 33: Inspector preserved over message from non-member *)
(* NOTE: Lemma 16 is not necessary *)
lemma (in Protocol) inspector_preserved_over_message_from_non_member :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<notin> v_set
  \<Longrightarrow> inspector (v_set, \<sigma>, p) 
  \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)"
proof - 
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V" "immediately_next_message (\<sigma>, m)" "sender m \<notin> v_set" "inspector (v_set, \<sigma>, p)" 
  (* 1. agreeing_validators preserved *)
  then have "\<forall> v \<in> v_set. v \<in> agreeing_validators (p, \<sigma>) \<longrightarrow> v \<in> agreeing_validators (p, \<sigma> \<union> {m})"
    using agreeing_status_of_non_sender_not_affected_by_minimal_transitions
    by blast
  (* 2. gt_threshold preserved *)
  moreover have "\<forall> v_set'. gt_threshold(v_set', \<sigma>) \<longrightarrow> gt_threshold(v_set', \<sigma> \<union> {m})"
  proof-
    have "equivocation_fault_weight ({m} \<union> \<sigma>) \<ge> equivocation_fault_weight \<sigma>"
      apply (rule equivocation_fault_weight_is_monotonic)
      apply auto
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> apply blast
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_by_immediately_next_message by auto
    hence "weight_measure V / 2 + t - equivocation_fault_weight \<sigma> \<ge> weight_measure V / 2 + t - equivocation_fault_weight ({m} \<union> \<sigma>)"
      by simp

    have p: "\<And>v_set'. weight_measure V / 2 + t - equivocation_fault_weight \<sigma> < weight_measure v_set' \<Longrightarrow> weight_measure V / 2 + t - equivocation_fault_weight ({m} \<union> \<sigma>) < weight_measure v_set'"
    proof-
      fix v_set'
      assume "weight_measure V / 2 + t - equivocation_fault_weight \<sigma> < weight_measure v_set'"
      thus "weight_measure V / 2 + t - equivocation_fault_weight ({m} \<union> \<sigma>) < weight_measure v_set'"
        using \<open>equivocation_fault_weight \<sigma> \<le> equivocation_fault_weight ({m} \<union> \<sigma>)\<close> by linarith
    qed

    show "\<forall> v_set'. gt_threshold(v_set', \<sigma>) \<longrightarrow> gt_threshold(v_set', \<sigma> \<union> {m})"
      apply (auto simp add: gt_threshold_def)
      using p
      apply simp
      done
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
      apply (auto simp add: observed_def)
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by auto
    ultimately have "is_singleton (L_H_M (\<sigma> \<union> {m}) (sender m))"
      using L_H_M_of_observed_non_equivocating_validator_is_singleton by blast
    show "m = the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))"
      by (metis \<open>is_singleton (L_H_M (\<sigma> \<union> {m}) (sender m))\<close> \<open>m \<in> L_H_M (\<sigma> \<union> {m}) (sender m)\<close> is_singleton_the_elem singletonD)
  qed
qed

lemma (in Protocol) new_justification_is_L_H_J_of_sender :
  "\<And>\<sigma> m. \<lbrakk> \<sigma> \<in> \<Sigma>; m \<in> M; immediately_next_message (\<sigma>, m); sender m \<notin> equivocating_validators ({m} \<union> \<sigma>) \<rbrakk>
  \<Longrightarrow> the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m"
proof-
  have "\<And>X x f. \<lbrakk> the_elem X = x; is_singleton X \<rbrakk> \<Longrightarrow> the_elem (f ` X) = f x"
    by (simp add: is_singleton_the_elem)

  fix \<sigma> m
  assume "\<sigma> \<in> \<Sigma>" "m \<in> M" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators ({m} \<union> \<sigma>)"
  have "m = the_elem (L_H_M ({m} \<union> \<sigma>) (sender m))"
    using Protocol.new_message_is_L_H_M_of_sender Protocol_axioms \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> \<open>sender m \<notin> equivocating_validators ({m} \<union> \<sigma>)\<close> by auto
  moreover have "is_singleton (L_H_M ({m} \<union> \<sigma>) (sender m))"
  proof-
    have "sender m \<in> observed_non_equivocating_validators ({m} \<union> \<sigma>)"
      apply (auto simp add: observed_def)
      using \<open>sender m \<notin> equivocating_validators ({m} \<union> \<sigma>)\<close> by auto
    thus ?thesis
      using L_H_M_of_observed_non_equivocating_validator_is_singleton \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> state_transition_by_immediately_next_message by auto
  qed
  ultimately show "the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m"
    unfolding L_H_J_def
    by (metis \<open>\<And>x f X. \<lbrakk>the_elem X = x; is_singleton X\<rbrakk> \<Longrightarrow> the_elem (f ` X) = f x\<close> sup.commute)
qed

(* Lemma 20: Latest honest messages from non-equivocating messages are either the same as in their previous
latest message, or later *)
lemma (in Protocol) L_H_M_of_others_for_sender_is_the_previous_one_or_later:
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> v \<in> observed_non_equivocating_validators \<sigma>
  \<Longrightarrow> sender m \<in> observed_non_equivocating_validators \<sigma>
  \<Longrightarrow> v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))
  \<Longrightarrow> v \<in> observed_non_equivocating_validators (justification m)
  \<Longrightarrow> the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)
        \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})"
  and "v \<in> observed_non_equivocating_validators \<sigma>" "sender m \<in> observed_non_equivocating_validators \<sigma>" "v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))" "v \<in> observed_non_equivocating_validators (justification m)"
  have "v \<notin> equivocating_validators \<sigma>"
    using \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> by blast

  have "sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})"
    apply (auto simp add: observed_def)
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by auto

  have "v \<notin> equivocating_validators (justification m)"
    by (meson \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v \<notin> equivocating_validators \<sigma>\<close> equivocating_validators_preserve_subset in_mono state_transition_by_immediately_next_message state_transition_is_immediately_next_message)

  have "the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m"
  proof-
    have "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})"
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by blast
    hence "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "\<sigma> \<in> \<Sigma>" "\<sigma> \<subseteq> \<sigma> \<union> {m}" "{m} \<subseteq> \<sigma> \<union> {m}" "\<sigma> \<inter> {m} = \<emptyset>"
      apply simp
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close>)
      apply auto[1]
      apply simp
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_only_made_by_immediately_next_message by auto
    hence "\<And>m1. \<lbrakk> m1 \<in> \<sigma>; sender m1 = sender m \<rbrakk> \<Longrightarrow> m1 \<in> justification m"
      using later_messages_from_non_equivocating_validator_include_all_earlier_messages by force
    hence "\<And>m1. \<lbrakk> m1 \<in> \<sigma>; sender m1 = sender m \<rbrakk> \<Longrightarrow> justification m1 \<subseteq> justification m"
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> justified_def monotonicity_of_justifications by blast
    moreover have "the_elem (L_H_M \<sigma> (sender m)) \<in> \<sigma>" "sender (the_elem (L_H_M \<sigma> (sender m))) = sender m"
      using L_H_M_is_in_the_state \<open>\<sigma> \<in> \<Sigma>\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply blast
      using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> sender_of_L_H_M by blast
    ultimately have "justification (the_elem (L_H_M \<sigma> (sender m))) \<subseteq> justification m"
      by auto
    moreover have "is_singleton (L_H_J \<sigma> (sender m))"
      using L_H_J_of_observed_non_equivocating_validator_is_singleton \<open>\<sigma> \<in> \<Sigma>\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> by blast
    ultimately show "the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m"
    proof-
      have "\<And>X Y f. \<lbrakk> is_singleton X; f (the_elem X) \<subseteq> Y \<rbrakk> \<Longrightarrow> the_elem (f ` X) \<subseteq> Y"
        by (metis image_empty image_insert is_singleton_the_elem the_elem_eq)
      thus ?thesis
        by (smt L_H_J_def L_H_M_of_observed_non_equivocating_validator_is_singleton \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>justification (the_elem (L_H_M \<sigma> (sender m))) \<subseteq> justification m\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close>)
    qed
  qed
  hence "justification m = the_elem (L_H_J \<sigma> (sender m)) \<union> (justification m - the_elem (L_H_J \<sigma> (sender m)))"
    by blast

  define New where "New \<equiv> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m)))"

  have set_split: "\<And>A B P. {x \<in> A \<union> B. P x} = {x \<in> A. P x} \<union> {x \<in> B. P x}"
    by blast

  { assume "New = \<emptyset>"

    have "L_H_M (justification m) v
        = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}
        \<union> {m1 \<in> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}"
    proof-
      have "v \<notin> equivocating_validators (justification m)"
        by (simp add: \<open>v \<notin> equivocating_validators (justification m)\<close>)
      hence "L_H_M (justification m) v = L_M (justification m) v"
        by (simp add: L_H_M_def)
      also have "\<dots> = {m1 \<in> from_sender (v, justification m). later_from (m1, v, justification m) = \<emptyset>}"
        by (auto simp add: L_M_def)
      also have "\<dots> = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m)) \<union> (justification m - the_elem (L_H_J \<sigma> (sender m)))). later_from (m1, v, justification m) = \<emptyset>}"
        using \<open>justification m = the_elem (L_H_J \<sigma> (sender m)) \<union> (justification m - the_elem (L_H_J \<sigma> (sender m)))\<close> by auto
      also have "\<dots> = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))) \<union> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}"
        apply (subst from_sender_split)
        apply simp
        done
      also have "\<dots> = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}
                    \<union> {m1 \<in> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}"
        by (rule set_split)
      finally show "L_H_M (justification m) v
        = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}
        \<union> {m1 \<in> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}"
        by simp
    qed
    moreover have "{m1 \<in> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset> } = \<emptyset>"
      using New_def \<open>New = \<emptyset>\<close> by blast
    ultimately have "L_H_M (justification m) v = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}"
      by (smt Diff_empty Diff_eq_empty_iff Diff_partition Un_commute empty_Diff)

    { fix m1
      have "later_from (m1, v, justification m) = {m' \<in> from_sender (v, justification m). justified m1 m'}"
        by (simp add: later_from_def from_sender_def justified_def)
      also have "\<dots> = {m' \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m)) \<union> (justification m - the_elem (L_H_J \<sigma> (sender m)))). justified m1 m'}"
        using \<open>justification m = the_elem (L_H_J \<sigma> (sender m)) \<union> (justification m - the_elem (L_H_J \<sigma> (sender m)))\<close> by auto
      also have "\<dots> = {m' \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))) \<union> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). justified m1 m'}"
        apply (subst from_sender_split)
        apply simp
        done
      also have "\<dots> = {m' \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). justified m1 m'} \<union> {m' \<in> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))). justified m1 m'}"
        by (rule set_split)
      also have "\<dots> = {m' \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). justified m1 m'}"
        using New_def \<open>New = \<emptyset>\<close> by blast
      also have "\<dots> = later_from (m1, v, the_elem (L_H_J \<sigma> (sender m)))"
        by (simp add: later_from_def from_sender_def)
      finally have "later_from (m1, v, justification m) = later_from (m1, v, the_elem (L_H_J \<sigma> (sender m)))"
        by simp
    }
    hence "\<And>m'. later_from (m', v, justification m) = later_from (m', v, the_elem (L_H_J \<sigma> (sender m)))"
      by simp
    hence "L_H_M (justification m) v = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, the_elem (L_H_J \<sigma> (sender m))) = \<emptyset>}"
      by (smt Collect_cong \<open>L_H_M (justification m) v = {m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). later_from (m1, v, justification m) = \<emptyset>}\<close>)
    also have "\<dots> = L_M (the_elem (L_H_J \<sigma> (sender m))) v"
      by (simp add: L_M_def)
    also have "\<dots> = L_H_M (the_elem (L_H_J \<sigma> (sender m))) v"
      apply (auto simp add: L_H_M_def)
      using \<open>the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m\<close> \<open>v \<notin> equivocating_validators (justification m)\<close> equivocating_validators_preserve_subset by blast
    finally have "the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)"
      by simp
  }
  hence "New = \<emptyset> \<Longrightarrow> the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)" by simp

  { assume "New \<noteq> \<emptyset>"
    have "v \<notin> equivocating_validators (justification m)" "the_elem (L_H_J \<sigma> (sender m)) \<in> \<Sigma>" "the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m"
      and "justification m - the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m" "the_elem (L_H_J \<sigma> (sender m)) \<inter> (justification m - the_elem (L_H_J \<sigma> (sender m))) = \<emptyset>"
      apply (simp add: \<open>v \<notin> equivocating_validators (justification m)\<close>)
      apply (rule L_H_J_is_state_if_exists)
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close>)
      using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply auto[1]
      apply (simp add: \<open>the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m\<close>)
      apply simp
      apply simp
      done
    hence "\<And>m'1 m'2. \<lbrakk> m'1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))); m'2 \<in> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m))) \<rbrakk> \<Longrightarrow> m'1 \<in> justification m'2"
      apply (simp add: from_sender_def)
      apply (meson DiffI Diff_disjoint Diff_subset later_messages_from_non_equivocating_validator_include_all_earlier_messages)
      done
    hence "\<And>m'1 m'2. \<lbrakk> m'1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))); m'2 \<in> New \<rbrakk> \<Longrightarrow> m'1 \<in> justification m'2"
      by (simp add: New_def)
    hence "\<And>m'. m' \<in> New \<Longrightarrow> the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<in> justification m'"
    proof-
      assume hyp: "\<And>m'1 m'2. m'1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))) \<Longrightarrow> m'2 \<in> New \<Longrightarrow> m'1 \<in> justification m'2"
      have "the_elem (L_H_J \<sigma> (sender m)) \<subseteq> \<sigma>"
        using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>the_elem (L_H_J \<sigma> (sender m)) \<subseteq> justification m\<close> state_transition_by_immediately_next_message state_transition_is_immediately_next_message by blast
      hence "v \<notin> equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))"
        using \<open>v \<notin> equivocating_validators \<sigma>\<close> equivocating_validators_preserve_subset by blast
      have "the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<in> the_elem (L_H_J \<sigma> (sender m))"
        apply (rule L_H_M_is_in_the_state)
        apply (simp add: \<open>the_elem (L_H_J \<sigma> (sender m)) \<in> \<Sigma>\<close>)
        apply auto
        apply (simp add: \<open>v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))\<close>)
        apply (simp add: \<open>v \<notin> equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))\<close>)
        done
      show "\<And>m'. m' \<in> New \<Longrightarrow> the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<in> justification m'"
        apply (rule hyp)
        apply (simp add: from_sender_def, auto)
        using \<open>the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<in> the_elem (L_H_J \<sigma> (sender m))\<close> apply blast
        using sender_of_L_H_M
        using \<open>the_elem (L_H_J \<sigma> (sender m)) \<in> \<Sigma>\<close> \<open>v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))\<close> \<open>v \<notin> equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))\<close> by blast
    qed
    hence "\<And>m'. m' \<in> New \<Longrightarrow> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) m'"
      by (simp add: justified_def)

    { assume "the_elem (L_H_M (justification m) v) \<notin> New" (is "?elem \<notin> New")
      hence "?elem \<notin> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m)))"
        by (simp add: New_def)
      hence "?elem \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m)))"
      proof-
        assume "?elem \<notin> from_sender (v, justification m - the_elem (L_H_J \<sigma> (sender m)))"
        moreover have "?elem \<in> justification m"
          apply (rule L_H_M_is_in_the_state)
          apply (simp add: M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close>)
          using \<open>v \<in> observed_non_equivocating_validators (justification m)\<close> apply blast
          done
        moreover have "sender ?elem = v"
          using M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>v \<in> observed_non_equivocating_validators (justification m)\<close> sender_of_L_H_M by blast
        ultimately show ?thesis
          by (simp add: from_sender_def)
      qed

      have "\<And>m1 m2. \<lbrakk> m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))); m2 \<in> New \<rbrakk> \<Longrightarrow> m1 \<in> justification m2"
        using \<open>\<And>m'2 m'1. \<lbrakk>m'1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))); m'2 \<in> New\<rbrakk> \<Longrightarrow> m'1 \<in> justification m'2\<close> by blast
      hence "\<forall>m1 \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m))). \<exists>m2 \<in> New. m1 \<in> justification m2"
        apply auto
        using \<open>New \<noteq> \<emptyset>\<close> by blast
      hence "\<exists>m2 \<in> New. ?elem \<in> justification m2"
        using \<open>the_elem (L_H_M (justification m) v) \<in> from_sender (v, the_elem (L_H_J \<sigma> (sender m)))\<close> by blast
      then obtain n where "n \<in> New" "?elem \<in> justification n"
        by auto
      hence "justified ?elem n"
        using justified_def by blast
      hence "n \<in> {m \<in> from_sender (v, New). justified ?elem m}"
      proof-
        assume "justified ?elem n"
        have "n \<in> from_sender (v, New)"
          using \<open>n \<in> New\<close>
          by (simp add: from_sender_def New_def)
        thus ?thesis
          using \<open>justified (the_elem (L_H_M (justification m) v)) n\<close> by blast
      qed
      hence "{m' \<in> from_sender (v, justification m). justified ?elem m'} \<noteq> \<emptyset>"
      proof-
        assume "n \<in> {m \<in> from_sender (v, New). justified ?elem m}"
        moreover have "New \<subseteq> justification m"
          by (simp add: New_def from_sender_def)
        ultimately have "n \<in> {m' \<in> from_sender (v, justification m). justified ?elem m'}"
          apply (simp add: from_sender_def)
          apply auto
          done
        thus "{m' \<in> from_sender (v, justification m). justified ?elem m'} \<noteq> \<emptyset>"
          by auto
      qed
      hence "later_from (?elem, v, justification m) \<noteq> \<emptyset>"
        by (auto simp add: later_from_def from_sender_def)
      hence False
        using L_H_M_have_no_later_messages M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>v \<in> observed_non_equivocating_validators (justification m)\<close> by blast
    }
    hence "the_elem (L_H_M (justification m) v) \<in> New"
      by blast

    have "\<And>m'. m' \<in> New \<Longrightarrow> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) m'"
      by (simp add: \<open>\<And>m'. m' \<in> New \<Longrightarrow> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) m'\<close>)
    hence "justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))"
      using \<open>the_elem (L_H_M (justification m) v) \<in> New\<close> by blast
  }
  hence "New \<noteq> \<emptyset> \<Longrightarrow> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))" by simp

  show "the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<or>
       justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))"
    using \<open>New = \<emptyset> \<Longrightarrow> the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)\<close> \<open>New \<noteq> \<emptyset> \<Longrightarrow> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))\<close> by blast
qed

(* Lemma 21 *)
lemma (in Protocol) justified_message_exists_in_later_from:
  "\<forall> \<sigma> m1 m2. \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> \<sigma>
  \<longrightarrow> justified m1 m2 
  \<longrightarrow> m2 \<in> later_from (m1, sender m2, \<sigma>)"
  by (simp add: later_from_def later_def from_sender_def)

(* Lemma 22. *)
lemma (in Protocol) latest_honest_message_agreeing_validators_is_agreeing: "\<lbrakk> \<sigma> \<in> \<Sigma>; v \<in> observed_non_equivocating_validators \<sigma>; p (est (the_elem (L_H_M \<sigma> v))) \<rbrakk> \<Longrightarrow> v \<in> agreeing_validators (p, \<sigma>)"
proof-
  assume "\<sigma> \<in> \<Sigma>" "v \<in> observed_non_equivocating_validators \<sigma>" "p (est (the_elem (L_H_M \<sigma> v)))"
  hence "v \<in> {v \<in> V. \<forall>m \<in> L_H_M \<sigma> v. p (est (m))}"
    apply auto
    apply (meson in_mono observed_type_for_state)
    by (metis Diff_iff L_H_M_def \<open>\<sigma> \<in> \<Sigma>\<close> \<open>p (est (the_elem (L_H_M \<sigma> v)))\<close> is_singleton_the_elem observed_non_equivocating_validators_have_one_latest_message singletonD)
  hence "v \<in> {v \<in> V. \<forall>c \<in> L_H_E \<sigma> v. p c}"
    by (simp add: L_H_E_def)
  thus "v \<in> agreeing_validators (p, \<sigma>)"
    apply (auto simp add: agreeing_validators_def)
    using \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> apply blast
    using \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> apply blast
    apply (simp add: agreeing_def)
    done
qed

lemma (in Protocol) latest_honest_message_is_in_justification: "\<lbrakk> \<sigma> \<in> \<Sigma>; immediately_next_message (\<sigma>, m); sender m \<in> observed_non_equivocating_validators \<sigma>; sender m \<notin> equivocating_validators (\<sigma> \<union> {m}) \<rbrakk> \<Longrightarrow> the_elem (L_H_M \<sigma> (sender m)) \<in> justification m"
by (smt L_H_M_is_in_the_state L_H_M_is_message_if_exists UnCI equivocating_validators_implies_either_justified in_mono insert_iff justified_def only_valid_message_is_justified sender_of_L_H_M state_is_in_pow_Mi state_transition_only_made_by_immediately_next_message)

lemma (in Protocol) observed_non_equivocating_transitive_justification: "\<lbrakk> v \<in> observed (justification m); m' \<in> M; m \<in> justification m'; v \<notin> equivocating_validators (justification m') \<rbrakk> \<Longrightarrow> v \<in> observed_non_equivocating_validators (justification m')"
proof-
  assume "v \<in> observed (justification m)" "m \<in> justification m'" "m' \<in> M" "v \<notin> equivocating_validators (justification m')"

  have "justification m \<subseteq> justification m'"
    apply (rule monotonicity_of_justifications)
    apply (simp add: \<open>m' \<in> M\<close>)
    apply (simp add: justified_def)
    by (simp add: \<open>m \<in> justification m'\<close>)

  obtain u where "u \<in> justification m" "v = sender u"
    using \<open>v \<in> observed (justification m)\<close>
    by (auto simp add: observed_def)
  hence "u \<in> justification m'"
    using \<open>justification m \<subseteq> justification m'\<close> by blast
  hence "v \<in> observed (justification m')"
    apply (simp add: observed_def)
    using \<open>v = sender u\<close> by blast

  show "v \<in> observed_non_equivocating_validators (justification m')"
    apply auto
    apply (simp add: \<open>v \<in> observed (justification m')\<close>)
    using \<open>v \<notin> equivocating_validators (justification m')\<close> by auto
qed

lemma the_elem_commute: "is_singleton X \<Longrightarrow> the_elem (f ` X) = f (the_elem X)"
  by (metis image_insert image_is_empty is_singleton_the_elem the_elem_eq)

lemma the_elem_imps_eq: "\<lbrakk> the_elem X = the_elem Y; is_singleton X; is_singleton Y \<rbrakk> \<Longrightarrow> X = Y"
  by (simp add: is_singleton_the_elem)

(* Lemma 23: Non-equivocating messages from member see all members agreeing *)
lemma (in Protocol) new_message_see_all_members_agreeing :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V 
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<in> v_set
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> inspector (v_set, \<sigma>, p)
  \<Longrightarrow> (\<exists>v_set' \<subseteq> v_set. gt_threshold (v_set', \<sigma>) \<and>
      (\<forall>v' \<in> v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m)))
        \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>) \<and> v_set' \<subseteq> agreeing_validators (p, justification m))"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V" "immediately_next_message (\<sigma>, m)" "sender m \<in> v_set" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "inspector (v_set, \<sigma>, p)"

  have "sender m \<in> observed_non_equivocating_validators \<sigma>"
    using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> inspector_imps_everyone_observed_non_equivocating by blast

  { have "(\<exists>v_set'\<subseteq>v_set.
                gt_threshold (v_set', \<sigma>) \<and>
                (\<forall>v'\<in>v_set'.
                    v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and>
                    later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>))"
      using \<open>inspector (v_set, \<sigma>, p)\<close>
      apply (simp add: inspector_def)
      using \<open>sender m \<in> v_set\<close> by blast
    then obtain "v_set'" where "v_set' \<subseteq> v_set" "gt_threshold (v_set', \<sigma>)" "(\<forall>v' \<in> v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>)"
      by auto

    { fix v'
      assume "v' \<in> v_set'"

      have "the_elem (L_H_J \<sigma> (sender m)) \<in> \<Sigma>"
        apply (rule L_H_J_is_state_if_exists)
        apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
        using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> by blast

      have "is_singleton (L_H_M \<sigma> (sender m))"
        using L_H_M_of_observed_non_equivocating_validator_is_singleton \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> by blast

      { have "v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m)))"
          using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close> by blast
        hence "v' \<in> observed_non_equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))"
          using agreeing_validators_are_observed_non_equivocating_validators
          using \<open>the_elem (L_H_J \<sigma> (sender m)) \<in> \<Sigma>\<close> by blast
        hence "v' \<in> observed (the_elem (L_H_J \<sigma> (sender m)))"
          by blast
      }
      hence "v' \<in> observed (the_elem (L_H_J \<sigma> (sender m)))"
        by simp
      then obtain m' where "sender m' = v'" "m' \<in> the_elem (L_H_J \<sigma> (sender m))"
        by (auto simp add: observed_def)
      hence "m' \<in> justification (the_elem (L_H_M \<sigma> (sender m)))"
        apply (simp add: L_H_J_def)
        by (simp add: the_elem_commute \<open>is_singleton (L_H_M \<sigma> (sender m))\<close>)

      { have "the_elem (L_H_M \<sigma> (sender m)) \<in> justification m"
          apply (rule latest_honest_message_is_in_justification)
          apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
          apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
          using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply auto[1]
          using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by blast
        hence "justification (the_elem (L_H_M \<sigma> (sender m))) \<subseteq> justification m"
          by (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> justified_def monotonicity_of_justifications)
        hence "m' \<in> justification m"
          using \<open>m' \<in> justification (the_elem (L_H_M \<sigma> (sender m)))\<close> by blast
        hence p: "v' \<in> observed (justification m)"
          apply (simp add: observed_def)
          using \<open>sender m' = v'\<close> by blast

        have "v' \<in> v_set"
          using \<open>v' \<in> v_set'\<close> \<open>v_set' \<subseteq> v_set\<close> by auto
        hence "v' \<notin> equivocating_validators \<sigma>"
          using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> inspector_imps_everyone_observed_non_equivocating by auto
        moreover have "justification m \<subseteq> \<sigma>"
          using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_is_immediately_next_message state_transition_only_made_by_immediately_next_message by blast
        ultimately have "v' \<notin> equivocating_validators (justification m)"
          using equivocating_validators_preserve_subset by blast

        have "v' \<in> observed_non_equivocating_validators (justification m)"
          apply auto
          apply (simp add: p)
          by (simp add: \<open>v' \<notin> equivocating_validators (justification m)\<close>)
      }
    }
    hence "\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)" by simp

    have "\<And>v'. v' \<in> v_set' \<Longrightarrow>
      the_elem (L_H_M (justification m) v') = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')
      \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')) (the_elem (L_H_M (justification m) v'))"
    apply (rule L_H_M_of_others_for_sender_is_the_previous_one_or_later)
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>v_set' \<subseteq> v_set\<close> apply blast
      apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
      apply (meson \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>v_set' \<subseteq> v_set\<close> agreeing_validators_are_observed_non_equivocating_validators in_mono inspector_imps_belonging_validator_is_agreeing)
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> inspector_imps_everyone_observed_non_equivocating apply blast
      apply (meson DiffD1 Protocol.L_H_J_is_state_if_exists Protocol_axioms \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> agreeing_validators_are_observed_non_equivocating_validators subset_iff)
      using \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> by auto

    { fix v'
      assume hyp: "v' \<in> v_set'" "the_elem (L_H_M (justification m) v') = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')"

      have "is_singleton (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')"
        apply (rule L_H_M_of_observed_non_equivocating_validator_is_singleton)
        using L_H_J_is_state_if_exists \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply blast
        using Protocol.L_H_J_is_state_if_exists Protocol_axioms \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> \<open>v' \<in> v_set'\<close> agreeing_validators_are_observed_non_equivocating_validators by blast
      moreover have "is_singleton (L_H_M (justification m) v')"
        apply (rule L_H_M_of_observed_non_equivocating_validator_is_singleton)
        apply (simp add: M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
        using \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> hyp(1) by blast
      ultimately have "L_H_M (justification m) v' = L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'"
        by (simp add: hyp(2) the_elem_imps_eq)

      hence "L_H_E (justification m) v' = L_H_E (the_elem (L_H_J \<sigma> (sender m))) v'"
        by (simp add: L_H_E_def)

      have "v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m)))"
        by (simp add: \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close>)
      hence "\<And>c. c \<in> L_H_E (the_elem (L_H_J \<sigma> (sender m))) v' \<Longrightarrow> p c"
        apply (simp add: agreeing_validators_def L_H_E_def agreeing_def)
        apply blast
        done
      hence "\<And>c. c \<in> L_H_E (justification m) v' \<Longrightarrow> p c"
        using \<open>L_H_E (justification m) v' = L_H_E (the_elem (L_H_J \<sigma> (sender m))) v'\<close> by blast
      hence "v' \<in> agreeing_validators (p, justification m)"
        apply (simp add: agreeing_validators_def agreeing_def)
        using \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> hyp(1) by auto
    }
    hence "\<And>v'. v' \<in> v_set' \<Longrightarrow> the_elem (L_H_M (justification m) v') = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v') \<Longrightarrow> v' \<in> agreeing_validators (p, justification m)"
      by simp

    { fix v'
      assume "v' \<in> v_set'" "justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')) (the_elem (L_H_M (justification m) v'))"

      have "is_singleton (L_H_M (justification m) v')"
        using L_H_M_of_observed_non_equivocating_validator_is_singleton M_type \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>v' \<in> v_set'\<close> by blast
      hence "\<And>x. x \<in> L_H_M (justification m) v' \<Longrightarrow> x = the_elem (L_H_M (justification m) v')"
        by (metis empty_iff insertE is_singleton_the_elem)

      have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>"
        using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close> by blast
      hence "\<And>m'. m' \<in> later_from (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) \<Longrightarrow> p (est m')"
        by (simp add: later_disagreeing_messages_def)
      have "p (est (the_elem (L_H_M (justification m) v')))"
      proof-
        have "the_elem (L_H_M (justification m) v') \<in> later_from (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>)"
          apply (auto simp add: later_from_def)
          using L_H_M_is_in_the_state M_type \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>v' \<in> v_set'\<close> state_transition_by_immediately_next_message state_transition_is_immediately_next_message apply blast
          using M_type \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>v' \<in> v_set'\<close> sender_of_L_H_M apply auto[1]
          by (simp add: \<open>justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')) (the_elem (L_H_M (justification m) v'))\<close>)
        thus ?thesis
          using \<open>\<And>m'. m' \<in> later_from (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) \<Longrightarrow> p (est m')\<close> by blast
      qed
      hence "v' \<in> agreeing_validators (p, justification m)"
        apply (auto simp add: agreeing_validators_def agreeing_def L_H_E_def)
        using \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> \<open>v' \<in> v_set'\<close> apply auto[1]
        using \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> observed_non_equivocating_validators (justification m)\<close> \<open>v' \<in> v_set'\<close> apply auto[1]
        using \<open>\<And>x. x \<in> L_H_M (justification m) v' \<Longrightarrow> x = the_elem (L_H_M (justification m) v')\<close> by blast
    }
    hence "\<And>v'. v' \<in> v_set' \<Longrightarrow> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')) (the_elem (L_H_M (justification m) v')) \<Longrightarrow> v' \<in> agreeing_validators (p, justification m)"
      by simp

    have "\<And>v'. v' \<in> v_set' \<Longrightarrow> v' \<in> agreeing_validators (p, justification m)"
      using \<open>\<And>v'. \<lbrakk>v' \<in> v_set'; justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')) (the_elem (L_H_M (justification m) v'))\<rbrakk> \<Longrightarrow> v' \<in> agreeing_validators (p, justification m)\<close> \<open>\<And>v'. \<lbrakk>v' \<in> v_set'; the_elem (L_H_M (justification m) v') = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')\<rbrakk> \<Longrightarrow> v' \<in> agreeing_validators (p, justification m)\<close> \<open>\<And>v'. v' \<in> v_set' \<Longrightarrow> the_elem (L_H_M (justification m) v') = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v') \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v')) (the_elem (L_H_M (justification m) v'))\<close> by blast
    hence "v_set' \<subseteq> agreeing_validators (p, justification m)"
      by auto

    have "(\<exists>v_set'\<subseteq>v_set.
                gt_threshold (v_set', \<sigma>) \<and>
                (\<forall>v'\<in>v_set'.
                    v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and>
                    later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset> \<and> v_set' \<subseteq> agreeing_validators (p, justification m)))"
      using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>gt_threshold (v_set', \<sigma>)\<close> \<open>v_set' \<subseteq> agreeing_validators (p, justification m)\<close> \<open>v_set' \<subseteq> v_set\<close> by blast
  }
  thus "(\<exists>v_set' \<subseteq> v_set. gt_threshold (v_set', \<sigma>) \<and>
      (\<forall>v' \<in> v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m)))
        \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>) \<and> v_set' \<subseteq> agreeing_validators (p, justification m))"
    by (meson subsetI)
qed

(* 7.4.3 Non-equivocating messages from member agree *)

(* Lemma 24: New messages from member is agreeing *)
lemma (in Protocol) new_message_from_member_see_itself_agreeing :
  "\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<in> v_set
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> inspector (v_set, \<sigma>, p)
  \<Longrightarrow> sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})"
proof-
  assume "\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V" "majority_driven p" "immediately_next_message (\<sigma>, m)" "sender m \<in> v_set" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "inspector (v_set, \<sigma>, p)"

  have "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V"
    using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> by fastforce
  have "\<sigma> \<in> \<Sigma>t"
    using \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M \<and> v_set \<subseteq> V\<close> by blast

  have "(\<exists>v_set' \<subseteq> v_set. gt_threshold (v_set', \<sigma>) \<and>
      (\<forall>v' \<in> v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m)))
        \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>) \<and> v_set' \<subseteq> agreeing_validators (p, justification m))"
    apply (rule new_message_see_all_members_agreeing)
    apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
    apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
    apply (simp add: \<open>sender m \<in> v_set\<close>)
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply blast
    apply (simp add: \<open>inspector (v_set, \<sigma>, p)\<close>)
    done
  then obtain v_set' where "v_set' \<subseteq> v_set" "gt_threshold (v_set', \<sigma>)" "(\<forall>v' \<in> v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m)))
        \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>) \<and> v_set' \<subseteq> agreeing_validators (p, justification m)"
    by auto

  have "majority (v_set', the_elem (L_H_J \<sigma> (sender m)))"
  proof-
    have "gt_threshold (v_set', \<sigma>)"
      using \<open>gt_threshold (v_set', \<sigma>)\<close> by auto
    hence "weight_measure V div 2 + t - equivocation_fault_weight \<sigma> < weight_measure v_set'"
      by (simp add: gt_threshold_def)
    moreover have "weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) div 2 < weight_measure V div 2 + t - equivocation_fault_weight \<sigma>"
    proof-
      have h: "weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) = weight_measure V - weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> (sender m))))"
        apply (rule weight_measure_subset_minus [symmetric])
        using L_H_J_is_state_if_exists \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> equivocating_validators_is_finite inspector_imps_everyone_observed_non_equivocating apply blast
        apply (simp add: V_type)
        using L_H_J_is_state_if_exists \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> equivocating_validators_type inspector_imps_everyone_observed_non_equivocating by blast
      have "equivocation_fault_weight \<sigma> < t"
        using \<open>\<sigma> \<in> \<Sigma>t\<close>
        by (simp add: \<Sigma>t_def is_faults_lt_threshold_def)
      hence "equivocation_fault_weight \<sigma> * 2 < t * 2"
        by simp
      moreover have "equivocation_fault_weight \<sigma> * 2 - equivocation_fault_weight (the_elem (L_H_J \<sigma> (sender m))) \<le> equivocation_fault_weight \<sigma> * 2"
        apply (simp add: equivocation_fault_weight_def)
        by (meson L_H_J_is_state_if_exists \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> equivocating_validators_type in_mono inspector_imps_everyone_observed_non_equivocating weight_positive)
      ultimately have "equivocation_fault_weight \<sigma> * 2 - equivocation_fault_weight (the_elem (L_H_J \<sigma> (sender m))) < t * 2"
        by simp
      thus ?thesis
        apply auto
        apply (simp add: h)
        apply (simp add: equivocation_fault_weight_def [symmetric])
        done
    qed
    ultimately show "majority (v_set', the_elem (L_H_J \<sigma> (sender m)))"
      by (simp add: majority_def)
  qed

  have "weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) \<le> weight_measure (equivocating_validators (justification m))"
  proof-
    have "is_singleton (L_H_J \<sigma> (sender m))"
      apply (rule L_H_J_of_observed_non_equivocating_validator_is_singleton)
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> inspector_imps_everyone_observed_non_equivocating by blast
    hence "the_elem (L_H_J \<sigma> (sender m)) = justification (the_elem (L_H_M \<sigma> (sender m)))"
      by (metis L_H_J_def L_H_M_of_observed_non_equivocating_validator_is_singleton \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> in_mono inspector_imps_everyone_observed_non_equivocating the_elem_commute)

    have "justification (the_elem (L_H_M \<sigma> (sender m))) \<subseteq> justification m"
      apply (rule monotonicity_of_justifications)
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
      apply (simp add: justified_def)
      apply (rule latest_honest_message_is_in_justification)
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
      apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
      apply (meson \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> in_mono inspector_imps_everyone_observed_non_equivocating)
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by blast
    hence "equivocating_validators (the_elem (L_H_J \<sigma> (sender m))) \<subseteq> equivocating_validators (justification m)"
    proof-
      have "\<And>x. x \<notin> equivocating_validators (justification m) \<Longrightarrow> x \<notin> equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))"
        by (metis \<open>justification (the_elem (L_H_M \<sigma> (sender m))) \<subseteq> justification m\<close> \<open>the_elem (L_H_J \<sigma> (sender m)) = justification (the_elem (L_H_M \<sigma> (sender m)))\<close> equivocating_validators_preserve_subset in_mono)
      thus ?thesis
        by blast
    qed
    thus "weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) \<le> weight_measure (equivocating_validators (justification m))"
      by (simp add: M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> weight_measure_subset_gte)
  qed

  have "majority (v_set', justification m)"
  proof-
    have "majority (v_set', the_elem (L_H_J \<sigma> (sender m)))"
      using \<open>majority (v_set', the_elem (L_H_J \<sigma> (sender m)))\<close> by blast
    hence "weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) div 2 < weight_measure v_set'"
      by (simp add: majority_def)
    hence "weight_measure V div 2 - weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) div 2 < weight_measure v_set'"
    proof-
      assume "weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) / 2 < weight_measure v_set'"
      have "weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) = weight_measure V - weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> (sender m))))"
      apply (rule weight_measure_subset_minus [symmetric])
        apply (meson Protocol.L_H_J_is_state_if_exists Protocol_axioms \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> equivocating_validators_is_finite in_mono inspector_imps_everyone_observed_non_equivocating)
        apply (simp add: V_type)
        using L_H_J_is_state_if_exists \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> equivocating_validators_type inspector_imps_everyone_observed_non_equivocating by blast
      thus ?thesis
        using \<open>weight_measure (V - equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) / 2 < weight_measure v_set'\<close> by linarith
    qed
    hence "weight_measure V div 2 - weight_measure (equivocating_validators (justification m)) div 2 < weight_measure v_set'"
      using \<open>weight_measure (equivocating_validators (the_elem (L_H_J \<sigma> (sender m)))) \<le> weight_measure (equivocating_validators (justification m))\<close> by linarith
    hence "weight_measure (V - equivocating_validators (justification m)) div 2 < weight_measure v_set'"
    proof-
      assume "weight_measure V div 2 - weight_measure (equivocating_validators (justification m)) div 2 < weight_measure v_set'"
      have "weight_measure (V - equivocating_validators (justification m)) = weight_measure V - weight_measure (equivocating_validators (justification m))"
        by (simp add: M_type Params.weight_measure_def V_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> sum_diff)
      thus ?thesis
        by (simp add: \<open>weight_measure V / 2 - weight_measure (equivocating_validators (justification m)) / 2 < weight_measure v_set'\<close> diff_divide_distrib)
    qed
    thus "majority (v_set', justification m)"
      by (simp add: majority_def)
  qed

  { have "v_set' \<subseteq> agreeing_validators (p, justification m)"
      by (simp add: \<open>(\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>) \<and> v_set' \<subseteq> agreeing_validators (p, justification m)\<close>)
    hence "weight_measure v_set' \<le> weight_measure (agreeing_validators (p, justification m))"
    proof-
      assume "v_set' \<subseteq> agreeing_validators (p, justification m)"
      show "weight_measure v_set' \<le> weight_measure (agreeing_validators (p, justification m))"
        apply (rule weight_measure_subset_gte)
        apply (simp add: M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close>)
        by (simp add: \<open>v_set' \<subseteq> agreeing_validators (p, justification m)\<close>)
    qed
    moreover have "weight_measure v_set' > weight_measure (V - equivocating_validators (justification m)) div 2"
      using \<open>majority (v_set', justification m)\<close>
      by (simp add: majority_def)
    ultimately have "weight_measure (agreeing_validators (p, justification m)) > weight_measure (V - equivocating_validators (justification m)) div 2"
      by linarith
    hence "majority (agreeing_validators (p, justification m), justification m)"
      by (simp add: majority_def)
    moreover have "\<And>\<sigma>'. \<lbrakk> \<sigma>' \<in> \<Sigma>; majority (agreeing_validators (p, \<sigma>'), \<sigma>') \<rbrakk> \<Longrightarrow> (\<And>c. c \<in> \<epsilon> \<sigma>' \<Longrightarrow> p c)"
      using Protocol.majority_driven_def Protocol_axioms \<open>majority_driven p\<close> by blast
    ultimately have "\<And>c. c \<in> \<epsilon> (justification m) \<Longrightarrow> p c"
      using M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> by blast
    moreover have "est m \<in> \<epsilon> (justification m)"
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> immediately_next_message_exists_in_same_depth by auto
    ultimately have "p (est m)"
      by blast
    hence "p (est (the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))))"
      using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> new_message_is_L_H_M_of_sender by auto
    have "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})"
    proof-
      have "\<sigma> \<union> {m} \<in> \<Sigma>"
        using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v_set \<subseteq> V\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_only_made_by_immediately_next_message by blast
      moreover have "sender m \<in> observed_non_equivocating_validators (\<sigma> \<union> {m})"
        apply (rule)
        apply (simp add: observed_def)
        apply blast
        using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by auto
      moreover have "p (est (the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))))"
        using \<open>p (est (the_elem (L_H_M (\<sigma> \<union> {m}) (sender m))))\<close> by blast
      ultimately show ?thesis
        using latest_honest_message_agreeing_validators_is_agreeing by blast
    qed
  }
  thus "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})" by simp
qed

(* 7.4.4 Honest messages from member do not break inspector *)

(* Lemma 25 *)
lemma (in Protocol) L_H_M_of_sender_is_previous_L_H_M :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M 
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> sender m \<in> observed_non_equivocating_validators \<sigma> 
  \<Longrightarrow> the_elem (L_H_M (justification m) (sender m)) = the_elem (L_H_M \<sigma> (sender m))"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})"
    and "sender m \<in> observed_non_equivocating_validators \<sigma> "

  have "justification m \<subseteq> \<sigma>"
    using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_is_immediately_next_message state_transition_only_made_by_immediately_next_message by blast
  hence "justification m \<subseteq> \<sigma> \<union> {m}"
    by blast
  hence "equivocating_validators (justification m) \<subseteq> equivocating_validators (\<sigma> \<union> {m})"
    using equivocating_validators_preserve_subset by auto
  hence "sender m \<notin> equivocating_validators (justification m)"
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by blast

  { assume "\<exists>m' \<in> from_sender (sender m, justification m). justified (the_elem (L_H_M \<sigma> (sender m))) m'"
    hence "\<exists>m' \<in> from_sender (sender m, \<sigma>). justified (the_elem (L_H_M \<sigma> (sender m))) m'"
      by (metis UnCI \<open>justification m \<subseteq> \<sigma>\<close> from_sender_split sup.absorb_iff1)
    hence "later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma>) \<noteq> \<emptyset>"
      apply (simp add: later_from_def from_sender_def)
      by auto
    have "later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma>) = \<emptyset>"
      apply (rule L_H_M_have_no_later_messages)
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
      using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> by auto
    hence "False"
      using \<open>later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma>) \<noteq> \<emptyset>\<close> by linarith
  }
  hence "\<not> (\<exists>m' \<in> from_sender (sender m, justification m). justified (the_elem (L_H_M \<sigma> (sender m))) m')"
    by blast
  hence "later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, justification m) = \<emptyset>"
    by (auto simp add: later_from_def from_sender_def)
  moreover have "the_elem (L_H_M \<sigma> (sender m)) \<in> from_sender (sender m, justification m)"
    apply (simp add: from_sender_def, rule)
    apply (rule latest_honest_message_is_in_justification)
    apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
    apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
    using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply auto[1]
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply blast
    using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> sender_of_L_H_M by auto
  ultimately have "the_elem (L_H_M \<sigma> (sender m)) \<in> L_M (justification m) (sender m)"
    using L_M_def by blast
  moreover have "L_H_M (justification m) (sender m) = L_M (justification m) (sender m)"
    by (simp add: L_H_M_def \<open>sender m \<notin> equivocating_validators (justification m)\<close>)
  ultimately have "the_elem (L_H_M \<sigma> (sender m)) \<in> L_H_M (justification m) (sender m)"
    by simp
  thus "the_elem (L_H_M (justification m) (sender m)) = the_elem (L_H_M \<sigma> (sender m))"
    by (metis Diff_iff L_H_M_of_observed_non_equivocating_validator_is_singleton L_M_from_non_observed_validator_is_empty M_type \<open>L_H_M (justification m) (sender m) = L_M (justification m) (sender m)\<close> \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>sender m \<notin> equivocating_validators (justification m)\<close> insert_absorb2 is_singletonI mk_disjoint_insert singleton_insert_inj_eq the_elem_eq the_elem_imps_eq)
qed

(* Lemma 26 *)
lemma (in Protocol) L_H_M_of_sender_justified_by_new_message :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M 
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> sender m \<in> observed_non_equivocating_validators \<sigma> 
  \<Longrightarrow> justified (the_elem (L_H_M \<sigma> (sender m))) m"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "sender m \<in> observed_non_equivocating_validators \<sigma> "
  have "\<And>m1 m2. \<lbrakk> m1 \<in> from_sender (sender m, \<sigma>); m2 \<in> from_sender (sender m, {m}) \<rbrakk> \<Longrightarrow> m1 \<in> justification m2"
    apply (auto simp add: from_sender_def)
    by (smt Un_iff \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> equivocating_validators_implies_either_justified insertCI justified_def state_is_in_pow_Mi state_transition_only_made_by_immediately_next_message subsetD)
  hence "\<And>m'. m' \<in> from_sender (sender m, \<sigma>) \<Longrightarrow> m' \<in> justification m"
    by (simp add: from_sender_def)
  moreover have "the_elem (L_H_M \<sigma> (sender m)) \<in> from_sender (sender m, \<sigma>)"
    apply (simp add: from_sender_def, rule)
    apply (rule L_H_M_is_in_the_state)
    using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> apply auto[1]
    using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply auto[1]
    using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> sender_of_L_H_M by blast
  ultimately have "the_elem (L_H_M \<sigma> (sender m)) \<in> justification m"
    by simp
  thus "justified (the_elem (L_H_M \<sigma> (sender m))) m"
    by (simp add: justified_def)
qed

(* Lemma 27: Nothing later than latest honest message *)
lemma (in Protocol) nothing_later_than_L_H_M :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V
  \<Longrightarrow> v \<in> observed_non_equivocating_validators \<sigma>
  \<Longrightarrow> later_from (the_elem (L_H_M \<sigma> v), v, \<sigma>) = \<emptyset>"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V" "v \<in> observed_non_equivocating_validators \<sigma>"
  have "L_H_M \<sigma> v = L_M \<sigma> v"
    using L_H_M_def \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> by auto
  hence "L_H_M \<sigma> v = {m \<in> from_sender (v, \<sigma>). later_from (m, v, \<sigma>) = \<emptyset>}"
    by (auto simp add: L_M_def)
  hence "the_elem (L_H_M \<sigma> v) = the_elem {m \<in> from_sender (v, \<sigma>). later_from (m, v, \<sigma>) = \<emptyset>}"
    by simp
  moreover have "is_singleton (L_H_M \<sigma> v)"
    apply (rule L_H_M_of_observed_non_equivocating_validator_is_singleton)
    apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close>)
    using \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> by auto
  ultimately show ?thesis
    using L_H_M_have_no_later_messages \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> by blast
qed

(* Lemma 28: Later messages for sender is just the new message *)
lemma (in Protocol) later_messages_for_sender_is_only_new_message :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M 
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> sender m \<in> observed_non_equivocating_validators \<sigma>
  \<Longrightarrow> later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma> \<union> {m}) = {m}"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "sender m \<in> observed_non_equivocating_validators \<sigma>"
  have "later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma> \<union> {m}) = {m' \<in> from_sender (sender m, \<sigma> \<union> {m}). justified (the_elem (L_H_M \<sigma> (sender m))) m'}"
    by (simp add: later_from_def justified_def from_sender_def)
  also have "\<dots> = {m' \<in> from_sender (sender m, \<sigma>). justified (the_elem (L_H_M \<sigma> (sender m))) m'} \<union> {m' \<in> from_sender (sender m, {m}). justified (the_elem (L_H_M \<sigma> (sender m))) m'}"
    apply (subst from_sender_split)
    by blast
  also have "\<dots> = {m' \<in> from_sender (sender m, \<sigma>). justified (the_elem (L_H_M \<sigma> (sender m))) m'} \<union> {m}"
  proof-
    have "{m' \<in> from_sender (sender m, {m}). justified (the_elem (L_H_M \<sigma> (sender m))) m'} = {m}"
      apply (auto simp add: from_sender_def)
      apply (rule L_H_M_of_sender_justified_by_new_message)
      apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
      apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
      using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply blast
      using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> by auto
    thus ?thesis
      by simp
  qed
  also have "\<dots> = later_from (the_elem (L_H_M \<sigma> (sender m)), sender m, \<sigma>) \<union> {m}"
    by (simp add: later_from_def from_sender_def)
  also have "\<dots> = {m}"
    using nothing_later_than_L_H_M
    using L_H_M_have_no_later_messages \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> by blast
  finally show ?thesis
    by simp
qed

(* Lemma 29: Later disagreeing is monotonic *)
lemma (in Protocol) later_disagreeing_is_monotonic:
  "v \<in> V \<and> \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> M
  \<Longrightarrow> justified m1 m2
  \<Longrightarrow> later_disagreeing_messages (p, m2, v, \<sigma>) \<subseteq> later_disagreeing_messages (p, m1, v, \<sigma>)"
  using message_in_state_is_strict_subset_of_the_state message_in_state_is_valid M_type state_is_in_pow_Mi  
  apply (simp add: later_disagreeing_messages_def later_from_def justified_def)
  by auto

(* Lemma 30 *)
lemma (in Protocol) previous_empty_later_disagreeing_messages_imps_empty_in_new_message :
  "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V 
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> sender m \<in> observed_non_equivocating_validators \<sigma>
  \<Longrightarrow> v \<in> observed_non_equivocating_validators \<sigma>
  \<Longrightarrow> v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))
  \<Longrightarrow> v \<in> observed_non_equivocating_validators (justification m)
  \<Longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)), v, \<sigma>) = \<emptyset>
  \<Longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (justification m) v)), v, \<sigma>) = \<emptyset>"
proof-
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V" "immediately_next_message (\<sigma>, m)" "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "sender m \<in> observed_non_equivocating_validators \<sigma>"
    and "v \<in> observed_non_equivocating_validators \<sigma>" "v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))" "v \<in> observed_non_equivocating_validators (justification m)"
    and "later_disagreeing_messages (p, (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)), v, \<sigma>) = \<emptyset>"

  have "the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)
    \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))"
    apply (rule L_H_M_of_others_for_sender_is_the_previous_one_or_later)
    apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close>)
    apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
    using \<open>v \<in> observed_non_equivocating_validators \<sigma>\<close> apply auto[1]
    using \<open>sender m \<in> observed_non_equivocating_validators \<sigma>\<close> apply auto[1]
    using \<open>v \<in> observed (the_elem (L_H_J \<sigma> (sender m)))\<close> apply blast
    using \<open>v \<in> observed_non_equivocating_validators (justification m)\<close> by blast

  { assume "the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)"
    hence "later_disagreeing_messages (p, (the_elem (L_H_M (justification m) v)), v, \<sigma>) = \<emptyset>"
      by (simp add: \<open>later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v), v, \<sigma>) = \<emptyset>\<close>)
  }
  hence "the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<Longrightarrow> later_disagreeing_messages (p, (the_elem (L_H_M (justification m) v)), v, \<sigma>) = \<emptyset>"
    by simp

  { assume "justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))"
    hence "the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<in> justification (the_elem (L_H_M (justification m) v))"
      by (simp add: justified_def)
    hence "later_disagreeing_messages (p, the_elem (L_H_M (justification m) v), v, \<sigma>) \<subseteq> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v), v, \<sigma>)"
      apply (rule_tac later_disagreeing_is_monotonic)
      using L_H_M_is_message_if_exists M_type Params.state_is_subset_of_M \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M \<and> v \<in> V\<close> \<open>v \<in> observed_non_equivocating_validators (justification m)\<close> apply blast
      using \<open>justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))\<close> by blast
    hence "later_disagreeing_messages (p, the_elem (L_H_M (justification m) v), v, \<sigma>) = \<emptyset>"
      by (simp add: \<open>later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v), v, \<sigma>) = \<emptyset>\<close>)
  }
  hence "justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v)) \<Longrightarrow> later_disagreeing_messages (p, the_elem (L_H_M (justification m) v), v, \<sigma>) = \<emptyset>"
    by simp

  show ?thesis
    using \<open>justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v)) \<Longrightarrow> later_disagreeing_messages (p, the_elem (L_H_M (justification m) v), v, \<sigma>) = \<emptyset>\<close> \<open>the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<Longrightarrow> later_disagreeing_messages (p, the_elem (L_H_M (justification m) v), v, \<sigma>) = \<emptyset>\<close> \<open>the_elem (L_H_M (justification m) v) = the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v) \<or> justified (the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v)) (the_elem (L_H_M (justification m) v))\<close> by blast
qed

(* Lemma 34: Inspector preserved over message from non-equivocating member *)
(* NOTE: Lemma 31 is not necessary*)
lemma (in Protocol) inspector_preserved_over_message_from_non_equivocating_member: "\<sigma> \<in> \<Sigma>t \<and> m \<in> M
  \<Longrightarrow> finite v_set
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<in> v_set
  \<Longrightarrow> sender m \<notin> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> inspector (v_set, \<sigma>, p)
  \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)"
proof-
  assume "\<sigma> \<in> \<Sigma>t \<and> m \<in> M" "finite v_set" "majority_driven p" "immediately_next_message (\<sigma>, m)" "sender m \<in> v_set"
  and "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})" "inspector (v_set, \<sigma>, p)"

  have "\<sigma> \<in> \<Sigma> \<and> m \<in> M"
    using \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close>
    by (simp add: \<Sigma>t_def)
  have hyp: "v_set \<noteq> \<emptyset> \<and> v_set \<subseteq> V \<and> (\<forall>v\<in>v_set.
    v \<in> agreeing_validators (p, \<sigma>) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma>) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)))"
    using \<open>inspector (v_set, \<sigma>, p)\<close> by (simp add: inspector_def)

  have eq_jm: "the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)) = justification m"
    apply (rule new_justification_is_L_H_J_of_sender)
    apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
    apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
    apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
    using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> by auto

  have "v_set \<noteq> \<emptyset>"
    using \<open>sender m \<in> v_set\<close> by auto
  moreover have "v_set \<subseteq> V"
    using hyp by auto
  moreover have "\<And>v. v \<in> v_set \<Longrightarrow>
    v \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"
  proof-
    { have "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})"
        apply (rule new_message_from_member_see_itself_agreeing [of _ _ v_set])
        using \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close> calculation(2) apply blast
        apply (simp add: \<open>majority_driven p\<close>)
        using \<open>immediately_next_message (\<sigma>, m)\<close> apply auto[1]
        apply (simp add: \<open>sender m \<in> v_set\<close>)
        using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
        apply (simp add: \<open>inspector (v_set, \<sigma>, p)\<close>)
        done
      moreover have "(\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"
      proof-
        have "\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma>) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>) \<and>
        v_set' \<subseteq> agreeing_validators (p, justification m)"
          apply (rule new_message_see_all_members_agreeing)
          apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>v_set \<subseteq> V\<close>)
             apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
          using \<open>sender m \<in> v_set\<close> apply blast
          using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply blast
          using \<open>inspector (v_set, \<sigma>, p)\<close> apply blast
          done
        then obtain v_set' where "v_set'\<subseteq>v_set" "gt_threshold (v_set', \<sigma>)" "(\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>)"
          "v_set' \<subseteq> agreeing_validators (p, justification m)"
          by blast

        have "gt_threshold (v_set', \<sigma> \<union> {m})"
        proof-
          have "gt_threshold (v_set', \<sigma>)"
            by (simp add: \<open>gt_threshold (v_set', \<sigma>)\<close>)
          hence "weight_measure V / 2 + t - equivocation_fault_weight \<sigma> < weight_measure v_set'"
            by (simp add: gt_threshold_def)
          moreover have "equivocation_fault_weight \<sigma> \<le> equivocation_fault_weight (\<sigma> \<union> {m})"
            apply (simp add: equivocation_fault_weight_def)
            apply (rule weight_measure_subset_gte)
             apply (rule equivocating_validators_type)
            using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_by_immediately_next_message apply auto[1]
            by (simp add: equivocating_validators_preserve_subset subset_insertI)
          ultimately have "weight_measure V / 2 + t - equivocation_fault_weight (\<sigma> \<union> {m}) < weight_measure v_set'"
            by linarith
          thus ?thesis
            by (simp add: gt_threshold_def)
        qed

        { fix v'
          assume "v' \<in> v_set'"
          have "v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>"
            using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close> by blast

          have "v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m)))"
            apply (subst new_justification_is_L_H_J_of_sender)
                apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
               apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close>)
              apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
            using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
            using \<open>v' \<in> v_set'\<close> \<open>v_set' \<subseteq> agreeing_validators (p, justification m)\<close> by blast
          moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', \<sigma> \<union> {m}) = \<emptyset>"
          proof-
            have "later_disagreeing_messages (p, the_elem (L_H_M (justification m) v'), v', \<sigma>) = \<emptyset>"
              apply (rule previous_empty_later_disagreeing_messages_imps_empty_in_new_message)
              using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>v' \<in> v_set'\<close> \<open>v_set \<subseteq> V\<close> \<open>v_set' \<subseteq> v_set\<close> apply blast
                     apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
              using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
              using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> inspector_imps_everyone_observed_non_equivocating apply blast
              using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>v' \<in> v_set'\<close> \<open>v_set' \<subseteq> v_set\<close> inspector_imps_everyone_observed_non_equivocating apply blast
                      apply (smt L_H_E_from_non_observed_validator_is_empty L_H_E_of_observed_non_equivocating_validator_is_singleton L_H_J_is_state_if_exists \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> \<open>v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close> \<open>v_set \<subseteq> V\<close> \<open>v_set' \<subseteq> v_set\<close> agreeing_validators_are_observed_non_equivocating_validators ex_in_conv inspector_imps_everyone_observed_non_equivocating is_singleton_the_elem singletonI subsetD)
              using M_type \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>v' \<in> v_set'\<close> \<open>v_set' \<subseteq> agreeing_validators (p, justification m)\<close> agreeing_validators_are_observed_non_equivocating_validators apply blast
              by (simp add: \<open>v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>\<close>)
            hence "later_disagreeing_messages (p, the_elem (L_H_M (justification m) v'), v', \<sigma>) = \<emptyset>"
              using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> new_justification_is_L_H_J_of_sender by auto
            moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', {m}) = \<emptyset>"
            proof-
              have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', {m}) \<subseteq> {m' \<in> {m}. \<not> p (est m')}"
                by (auto simp add: later_disagreeing_messages_def later_from_def)

              have "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})"
                by fact
              hence "agreeing (p, \<sigma> \<union> {m}, sender m)"
                by (simp add: agreeing_validators_def)
              moreover have "m \<in> L_H_M ({m} \<union> \<sigma>) (sender m)"
                apply (auto simp add: L_H_M_def L_M_def from_sender_def later_from_def)
                using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
                 apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> message_cannot_justify_itself)
                by (meson \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> in_mono justified_def state_is_in_pow_Mi state_transition_only_made_by_immediately_next_message)
              ultimately have "p (est m)"
                by (simp add: agreeing_def L_H_E_def)

              have "v' \<noteq> sender m \<Longrightarrow> later_disagreeing_messages (p, the_elem (L_H_M (justification m) v'), v', {m}) = \<emptyset>"
                by (auto simp add: later_disagreeing_messages_def later_from_def)
              moreover have "later_disagreeing_messages (p, the_elem (L_H_M (justification m) (sender m)), sender m, {m}) = \<emptyset>"
                apply (auto simp add: later_disagreeing_messages_def later_from_def)
                by (simp add: \<open>p (est m)\<close>)
              ultimately show ?thesis
                using eq_jm by auto
            qed
            moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', \<sigma> \<union> {m})
              = later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', \<sigma>) \<union> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', {m})"
              by (auto simp add: later_disagreeing_messages_def later_from_def)
            ultimately show "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', \<sigma> \<union> {m}) = \<emptyset>"
              using eq_jm by auto              
          qed
          ultimately have "v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', \<sigma> \<union> {m}) = \<emptyset>"
            by simp
        }
        hence "\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', (\<sigma> \<union> {m})) = \<emptyset>"
          by auto

        show ?thesis
          using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', \<sigma> \<union> {m}) = \<emptyset>\<close> \<open>gt_threshold (v_set', \<sigma> \<union> {m})\<close> \<open>v_set' \<subseteq> v_set\<close> by blast
      qed
      ultimately have "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"
        by simp
    }
    hence p: "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) (sender m))) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"  by simp

    have "p (est m)"
    proof-
      have "sender m \<in> agreeing_validators (p, \<sigma> \<union> {m})"
        using p by blast
      hence "agreeing (p, \<sigma> \<union> {m}, sender m)"
        by (simp add: agreeing_validators_def)
      moreover have "m \<in> L_H_M ({m} \<union> \<sigma>) (sender m)"
        apply (auto simp add: L_H_M_def L_M_def from_sender_def later_from_def)
        using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
         apply (simp add: \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> message_cannot_justify_itself)
        by (meson \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> in_mono justified_def state_is_in_pow_Mi state_transition_only_made_by_immediately_next_message)
      ultimately show "p (est m)"
        by (simp add: agreeing_def L_H_E_def)
    qed

    fix v
    assume "v \<in> v_set"

    { assume "v \<noteq> sender m"
      have v_LHM: "L_H_M (\<sigma> \<union> {m}) v = L_H_M \<sigma> v"
        apply (auto simp add: L_H_M_def)
        using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> equivocating_validators_preserved_over_honest_message apply force
        using equivocating_validators_preserve_subset insertI2 apply blast
        apply (auto simp add: L_M_def from_sender_def)
        using \<open>v \<noteq> sender m\<close> apply blast
        using \<open>v \<noteq> sender m\<close> apply blast
        apply (auto simp add: later_from_def)
        using \<open>v \<noteq> sender m\<close> by auto
      have v_LHJ: "L_H_J (\<sigma> \<union> {m}) v = L_H_J \<sigma> v"
        apply (simp add: L_H_J_def)
        using v_LHM by auto

      have "v \<in> agreeing_validators (p, \<sigma>) \<and> (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma>) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))"
        using \<open>v \<in> v_set\<close> hyp by blast
      then obtain v_set' where "v_set'\<subseteq>v_set" "gt_threshold (v_set', \<sigma>)" "(\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)"
        by blast

      have "v \<in> agreeing_validators (p, \<sigma> \<union> {m})"
      proof-
        have "v \<in> agreeing_validators (p, \<sigma>)"
          by (simp add: \<open>v \<in> agreeing_validators (p, \<sigma>) \<and> (\<exists>v_set'\<subseteq>v_set. gt_threshold (v_set', \<sigma>) \<and> (\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))\<close>)
        thus ?thesis
          apply (auto simp add: agreeing_validators_def)
          using observed_def apply auto[1]
          using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> equivocating_validators_preserved_over_honest_message apply force
          apply (auto simp add: agreeing_def L_H_E_def)
          using v_LHM by simp
      qed
      moreover have "(\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"
      proof-
        have "gt_threshold (v_set', \<sigma> \<union> {m})"
        proof-
          have "gt_threshold (v_set', \<sigma>)"
            by (simp add: \<open>gt_threshold (v_set', \<sigma>)\<close>)
          hence "weight_measure V / 2 + t - equivocation_fault_weight \<sigma> < weight_measure v_set'"
            by (simp add: gt_threshold_def)
          moreover have "equivocation_fault_weight \<sigma> \<le> equivocation_fault_weight (\<sigma> \<union> {m})"
            apply (simp add: equivocation_fault_weight_def)
            apply (rule weight_measure_subset_gte)
             apply (rule equivocating_validators_type)
            using \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> M\<close> \<open>immediately_next_message (\<sigma>, m)\<close> state_transition_by_immediately_next_message apply auto[1]
            by (simp add: equivocating_validators_preserve_subset subset_insertI)
          ultimately have "weight_measure V / 2 + t - equivocation_fault_weight (\<sigma> \<union> {m}) < weight_measure v_set'"
            by linarith
          thus ?thesis
            by (simp add: gt_threshold_def)
        qed

        { fix v'
          assume "v' \<in> v_set'"

          have "v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v))"
            apply (subst v_LHJ)
            using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close> by blast
          moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>"
          proof-
            have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma>) = \<emptyset>"
              apply (subst v_LHJ)
              using \<open>\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'\<close> by blast
            moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', {m}) = \<emptyset>"
              apply (subst v_LHJ)
              apply (auto simp add: later_disagreeing_messages_def later_from_def)
              using \<open>p (est m)\<close> by blast
            moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma> \<union> {m})
              = later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma>) \<union> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', {m})"
                by (auto simp add: later_disagreeing_messages_def later_from_def)
            ultimately show ?thesis
              by simp
          qed
          ultimately have "v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>" by simp
        }
        moreover hence "\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>"
          by simp
        ultimately show ?thesis
          using \<open>gt_threshold (v_set', \<sigma> \<union> {m})\<close> \<open>v_set' \<subseteq> v_set\<close> by blast
      qed
      ultimately have "v \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"
        by simp
    }
    hence q: "v \<noteq> sender m \<Longrightarrow> v \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
  (\<exists>v_set'\<subseteq>v_set.
      gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
      (\<forall>v'\<in>v_set'.
          v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
          later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', \<sigma> \<union> {m}) = \<emptyset>))" by simp

    show "v \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>))"
      using p q by auto
  qed

  ultimately have "v_set \<noteq> \<emptyset> \<and> v_set \<subseteq> V \<and> (\<forall>v\<in>v_set.
    v \<in> agreeing_validators (p, \<sigma> \<union> {m}) \<and>
    (\<exists>v_set'\<subseteq>v_set.
        gt_threshold (v_set', \<sigma> \<union> {m}) \<and>
        (\<forall>v'\<in>v_set'.
            v' \<in> agreeing_validators (p, the_elem (L_H_J (\<sigma> \<union> {m}) v)) \<and>
            later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J (\<sigma> \<union> {m}) v)) v'), v', (\<sigma> \<union> {m})) = \<emptyset>)))"
    by auto
  thus "inspector (v_set, \<sigma> \<union> {m}, p)"
    by (simp add: inspector_def)
qed

(* ###################################################### *)
(* 7.5 Equivocations from member do not break inspector *)
(* ###################################################### *)

lemma (in Protocol) weight_measure_inequality_whenever_incorrectly_minus_element: "\<lbrakk> finite A; v \<in> V \<rbrakk> \<Longrightarrow> weight_measure (A - {v}) \<ge> weight_measure A - W v"
  apply (cases "v \<in> A")
  apply (simp add: weight_measure_def)
  apply (simp add: sum_diff1)
  apply simp
  apply (simp add: W_type dual_order.strict_implies_order)
  done

lemma (in Protocol) gt_threshold_cannot_hold_with_empty_state: "\<sigma> \<in> \<Sigma>t \<Longrightarrow> \<not> gt_threshold (\<emptyset>, \<sigma>)"
  apply (auto simp add: gt_threshold_def weight_measure_def \<Sigma>t_def is_faults_lt_threshold_def)
  using t_type(2)
  using Protocol.t_type(1) Protocol_axioms by fastforce

lemma (in Protocol) weight_measure_implies_non_empty: "weight_measure S > 0 \<Longrightarrow> S \<noteq> \<emptyset>"
  apply (simp add: weight_measure_def)
  by auto

lemma (in Protocol) agreeing_implies_non_equivocating: "v \<in> agreeing_validators (p, \<sigma>) \<Longrightarrow> v \<notin> equivocating_validators \<sigma>"
  by (simp add: agreeing_validators_def)

lemma (in Protocol) gt_threshold_rhs_positive:
  "\<sigma> \<in> \<Sigma>t \<Longrightarrow> weight_measure V div 2 + t - equivocation_fault_weight \<sigma> > 0"
  apply (simp add: gt_threshold_def \<Sigma>t_def is_faults_lt_threshold_def weight_measure_def)
  using t_type(1) t_type(2) by linarith

lemma (in Protocol) gt_threshold_transitive: "\<lbrakk> v_set' \<subseteq> V; v_set \<subseteq> v_set'; gt_threshold (v_set, \<sigma>) \<rbrakk> \<Longrightarrow> gt_threshold (v_set', \<sigma>)"
  apply (simp add: gt_threshold_def)
  by (smt weight_measure_subset_gte)

(* Lemma 35: Inspector preserved over message from equivocating member *)
lemma (in Protocol) inspector_preserved_over_message_from_equivocating_member :
  "\<sigma> \<in> \<Sigma>
  \<Longrightarrow> m \<in> M
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> sender m \<in> equivocating_validators (\<sigma> \<union> {m})
  \<Longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>t
  \<Longrightarrow> vinspector_with \<sigma> p (\<lambda>v_set. sender m \<in> v_set \<and> finite v_set)
  \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p"
  (* Since \<sigma> \<union> {m} \<in> \<Sigma>t, gt_threshold still holds  *)
proof-
  assume "\<sigma> \<in> \<Sigma>" "m \<in> M" "majority_driven p" "immediately_next_message (\<sigma>, m)"
  and "sender m \<in> equivocating_validators (\<sigma> \<union> {m})" "\<sigma> \<union> {m} \<in> \<Sigma>t" "vinspector_with \<sigma> p (\<lambda>v_set. sender m \<in> v_set \<and> finite v_set)"
  
  obtain v_set where "v_set \<noteq> \<emptyset>" "v_set \<subseteq> V" "sender m \<in> v_set" "finite v_set" "inspector (v_set, \<sigma>, p)"
    using \<open>vinspector_with \<sigma> p (\<lambda>v_set. sender m \<in> v_set \<and> finite v_set)\<close>
    apply (simp add: vinspector_with_def)
    by (metis \<open>\<sigma> \<in> \<Sigma>\<close> agreeing_validators_type equals0D inspector_imps_everyone_agreeing subset_trans)
  hence "sender m \<in> agreeing_validators (p, \<sigma>) \<and> (\<exists>v_set'\<subseteq>v_set. gt_threshold (v_set', \<sigma>)
    \<and> (\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>))"
    by (simp add: inspector_def)
  then obtain v_set' where
    "v_set' \<subseteq> v_set" "gt_threshold (v_set', \<sigma>)"
    "(\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>)"
    by auto

  have "sender m \<notin> equivocating_validators \<sigma>"
    using \<open>sender m \<in> agreeing_validators (p, \<sigma>) \<and> (\<exists>v_set'\<subseteq>v_set. gt_threshold (v_set', \<sigma>) \<and> (\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> (sender m))) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> (sender m))) v'), v', \<sigma>) = \<emptyset>))\<close> agreeing_implies_non_equivocating by auto

  have "\<And>v_set'. \<lbrakk> gt_threshold (v_set', \<sigma>); v_set' \<subseteq> v_set \<rbrakk> \<Longrightarrow> gt_threshold (v_set' - {sender m}, \<sigma> \<union> {m})"
  proof-
    fix v_set'
    assume "gt_threshold (v_set', \<sigma>)" "v_set' \<subseteq> v_set"

    have "finite v_set'"
      using \<open>finite v_set\<close> \<open>v_set' \<subseteq> v_set\<close> finite_subset by blast
    hence "weight_measure (v_set' - {sender m}) \<ge> weight_measure v_set' - W (sender m)"
      using M_type \<open>m \<in> M\<close> weight_measure_inequality_whenever_incorrectly_minus_element by blast
    moreover have "weight_measure v_set' - W (sender m) > weight_measure V / 2 + t - equivocation_fault_weight \<sigma> - W (sender m)"
      using \<open>gt_threshold (v_set', \<sigma>)\<close>
      by (simp add: gt_threshold_def)
    moreover have "weight_measure V / 2 + t - equivocation_fault_weight \<sigma> - W (sender m) = weight_measure V / 2 + t - equivocation_fault_weight ({m} \<union> \<sigma>)"
    proof-
      have "equivocating_validators ({m} \<union> \<sigma>) = equivocating_validators \<sigma> \<union> {sender m}"
        using \<open>sender m \<in> equivocating_validators (\<sigma> \<union> {m})\<close> equivocating_validators_split_over_equivocating_message by auto
      hence "equivocation_fault_weight ({m} \<union> \<sigma>) = equivocation_fault_weight \<sigma> + W (sender m)"
        apply (simp add: equivocation_fault_weight_def weight_measure_def)
        using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>sender m \<notin> equivocating_validators \<sigma>\<close> equivocating_validators_is_finite by auto
      thus ?thesis
        by simp
    qed
    ultimately show "gt_threshold (v_set' - {sender m}, \<sigma> \<union> {m})"
      by (simp add: gt_threshold_def)
  qed
  hence "gt_threshold (v_set' - {sender m}, \<sigma> \<union> {m})"
    using \<open>gt_threshold (v_set', \<sigma>)\<close> \<open>v_set' \<subseteq> v_set\<close> by blast

  have "inspector (v_set - {sender m}, \<sigma> \<union> {m}, p)"
  proof-
    have "\<not> v_set \<subseteq> {sender m}"
    proof-
      have "weight_measure (v_set' - {sender m}) > 0"
        using \<open>gt_threshold (v_set' - {sender m}, \<sigma> \<union> {m})\<close>
        apply (simp add: gt_threshold_def)
        using gt_threshold_rhs_positive [OF \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close>]
        by auto
      hence "v_set' - {sender m} \<noteq> \<emptyset>"
        using weight_measure_implies_non_empty by blast
      hence "v_set - {sender m} \<noteq> \<emptyset>"
        using \<open>v_set' \<subseteq> v_set\<close> by auto
      thus ?thesis
        by auto
    qed
    moreover have "v_set - {sender m} \<subseteq> V"
      using \<open>v_set \<subseteq> V\<close> by auto
    moreover have "(\<forall>v\<in>v_set - {sender m}.
        v \<in> agreeing_validators (p, {m} \<union> \<sigma>) \<and>
        (\<exists>v_set'\<subseteq>v_set - {sender m}.
            gt_threshold (v_set', {m} \<union> \<sigma>) \<and>
            (\<forall>v'\<in>v_set'.
                v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v)) \<and>
                later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J ({m} \<union> \<sigma>) v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>)))"
      apply (rule, rule)
    proof-
      have "\<And>v. v \<in> v_set \<Longrightarrow> v \<in> agreeing_validators (p, \<sigma>)"
        using \<open>inspector (v_set, \<sigma>, p)\<close>
        by (simp add: inspector_def)
      show "\<And>v. v \<in> v_set - {sender m} \<Longrightarrow> v \<in> agreeing_validators (p, {m} \<union> \<sigma>)"
      proof-
        fix v
        assume "v \<in> v_set - {sender m}"
        have "v \<in> agreeing_validators (p, \<sigma>)"
          using \<open>\<And>va. va \<in> v_set \<Longrightarrow> va \<in> agreeing_validators (p, \<sigma>)\<close> \<open>v \<in> v_set - {sender m}\<close> by auto
        thus "v \<in> agreeing_validators (p, {m} \<union> \<sigma>)"
          using agreeing_status_of_non_sender_not_affected_by_minimal_transitions
          by (metis (no_types, hide_lams) DiffI Diff_iff Un_commute \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> \<open>v \<in> v_set - {sender m}\<close> agreeing_validatros_subset_of_validators in_mono)
      qed
    next
      fix v
      assume "v \<in> v_set - {sender m}"
      hence "v \<in> agreeing_validators (p, \<sigma>) \<and> (\<exists>v_set'\<subseteq>v_set. gt_threshold (v_set', \<sigma>) \<and> (\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))"
        using \<open>inspector (v_set, \<sigma>, p)\<close>
        by (simp add: inspector_def)
      then obtain v_set'' where
        "v_set'' \<subseteq> v_set" "gt_threshold (v_set'', \<sigma>)"
        "(\<forall>v'\<in>v_set''. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>)"
        by auto

      have "v_set'' - {sender m} \<subseteq> v_set - {sender m}"
        by (simp add: Diff_mono \<open>v_set'' \<subseteq> v_set\<close>)
      moreover have "gt_threshold (v_set'' - {sender m}, {m} \<union> \<sigma>)"
        using \<open>\<And>v_set'. \<lbrakk>gt_threshold (v_set', \<sigma>); v_set' \<subseteq> v_set\<rbrakk> \<Longrightarrow> gt_threshold (v_set' - {sender m}, \<sigma> \<union> {m})\<close> \<open>gt_threshold (v_set'', \<sigma>)\<close> \<open>v_set'' \<subseteq> v_set\<close> by auto
      moreover have "\<forall>v'\<in>v_set'' - {sender m}.
        v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v)) \<and>
        later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J ({m} \<union> \<sigma>) v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>"
      proof rule
        fix v'
        assume "v' \<in> v_set'' - {sender m}"

        have "L_H_J \<sigma> v = L_H_J ({m} \<union> \<sigma>) v"
          using L_H_J_of_non_sender_not_affected_by_minimal_transitions
          apply auto
          using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> \<open>v \<in> v_set - {sender m}\<close> \<open>v_set - {sender m} \<subseteq> V\<close> apply auto[1]
          using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>immediately_next_message (\<sigma>, m)\<close> \<open>m \<in> M\<close> \<open>v \<in> v_set - {sender m}\<close> \<open>v_set - {sender m} \<subseteq> V\<close> by auto
        moreover have "v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v))"
          using \<open>\<forall>v'\<in>v_set''. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'' - {sender m}\<close> by auto
        ultimately have "v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v))"
          by simp

        have "\<sigma> \<in> \<Sigma>" "the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v') \<in> M" "m \<in> M" "v' \<in> V"
          apply (simp add: \<open>\<sigma> \<in> \<Sigma>\<close>)
          apply (metis L_H_J_is_state_if_exists L_H_M_is_message_if_exists \<open>L_H_J \<sigma> v = L_H_J ({m} \<union> \<sigma>) v\<close> \<open>\<sigma> \<in> \<Sigma>\<close> \<open>v \<in> agreeing_validators (p, \<sigma>) \<and> (\<exists>v_set'\<subseteq>v_set. gt_threshold (v_set', \<sigma>) \<and> (\<forall>v'\<in>v_set'. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))\<close> \<open>v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v))\<close> agreeing_validators_are_observed_non_equivocating_validators subsetD)
          using \<open>m \<in> M\<close> apply blast
          using \<open>v' \<in> v_set'' - {sender m}\<close> \<open>v_set \<subseteq> V\<close> \<open>v_set'' \<subseteq> v_set\<close> by auto
        moreover have "v' \<in> V - {sender m}"
          using \<open>v' \<in> v_set'' - {sender m}\<close> calculation(4) by auto
        moreover have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>"
          using \<open>\<forall>v'\<in>v_set''. v' \<in> agreeing_validators (p, the_elem (L_H_J \<sigma> v)) \<and> later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', \<sigma>) = \<emptyset>\<close> \<open>v' \<in> v_set'' - {sender m}\<close> by auto
        ultimately have "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J \<sigma> v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>"
          using later_disagreeing_of_non_sender_not_affected_by_minimal_transitions
          using \<open>immediately_next_message (\<sigma>, m)\<close> by auto
        hence "later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J ({m} \<union> \<sigma>) v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>"
          by (simp add: \<open>L_H_J \<sigma> v = L_H_J ({m} \<union> \<sigma>) v\<close>)

        show "v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v)) \<and>
          later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J ({m} \<union> \<sigma>) v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>"
          using \<open>later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J ({m} \<union> \<sigma>) v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>\<close> \<open>v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v))\<close> by blast
      qed
      ultimately show "\<exists>v_set'\<subseteq>v_set - {sender m}. gt_threshold (v_set', {m} \<union> \<sigma>) \<and>
            (\<forall>v'\<in>v_set'.
                v' \<in> agreeing_validators (p, the_elem (L_H_J ({m} \<union> \<sigma>) v)) \<and>
                later_disagreeing_messages (p, the_elem (L_H_M (the_elem (L_H_J ({m} \<union> \<sigma>) v)) v'), v', {m} \<union> \<sigma>) = \<emptyset>)"
        by blast
    qed
    ultimately show "inspector (v_set - {sender m}, \<sigma> \<union> {m}, p)"
      apply (simp add: inspector_def)
      done
  qed
  thus "vinspector (\<sigma> \<union> {m}) p"
    using vinspector_def
    by (meson Diff_subset \<open>v_set \<subseteq> V\<close> subset_trans)
qed

(* Lemma 36 *)
lemma (in Protocol) inspector_preserved_over_immediately_next_message :
  "\<sigma> \<in> \<Sigma>t \<and> m \<in> M
  \<Longrightarrow> \<sigma> \<union> {m} \<in> \<Sigma>t
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> immediately_next_message (\<sigma>, m)
  \<Longrightarrow> vinspector \<sigma> p 
  \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p"
proof-
  assume "\<sigma> \<in> \<Sigma>t \<and> m \<in> M" "\<sigma> \<union> {m} \<in> \<Sigma>t" "majority_driven p"
    and "immediately_next_message (\<sigma>, m)" "vinspector \<sigma> p"
  have "\<sigma> \<in> \<Sigma>"
    using \<Sigma>t_def
    using \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close> by blast

  { assume "sender m \<notin> equivocating_validators (\<sigma> \<union> {m})"
    obtain v_set where "v_set \<subseteq> V" "inspector (v_set, \<sigma>, p)"
      using \<open>vinspector \<sigma> p\<close> vinspector_def
      by blast

    { assume "sender m \<in> v_set"
      have "inspector (v_set, \<sigma> \<union> {m}, p)"
        apply (rule inspector_preserved_over_message_from_non_equivocating_member)
        apply (simp add: \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close>)
        using V_type \<open>v_set \<subseteq> V\<close> rev_finite_subset apply auto[1]
        using \<open>majority_driven p\<close> apply auto[1]
        apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
        apply (simp add: \<open>sender m \<in> v_set\<close>)
        using \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m})\<close> apply auto[1]
        by (simp add: \<open>inspector (v_set, \<sigma>, p)\<close>)
    }
    hence "sender m \<in> v_set \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)" by simp

    { assume "sender m \<notin> v_set"
      have "inspector (v_set, \<sigma> \<union> {m}, p)"
        apply (rule inspector_preserved_over_message_from_non_member)
        using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close> \<open>v_set \<subseteq> V\<close> apply fastforce
        apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
        apply (simp add: \<open>sender m \<notin> v_set\<close>)
        using \<open>inspector (v_set, \<sigma>, p)\<close> by auto
    }
    hence "sender m \<notin> v_set \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)" by simp

    have "inspector (v_set, \<sigma> \<union> {m}, p)"
      using \<open>sender m \<in> v_set \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)\<close> \<open>sender m \<notin> v_set \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)\<close> by blast
    hence "vinspector (\<sigma> \<union> {m}) p"
      apply (simp add: vinspector_def)
      using \<open>v_set \<subseteq> V\<close> by auto
  }
  hence "sender m \<notin> equivocating_validators (\<sigma> \<union> {m}) \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p" by simp

  { assume "sender m \<in> equivocating_validators (\<sigma> \<union> {m})"
    obtain v_set where "v_set \<subseteq> V" "inspector (v_set, \<sigma>, p)"
      using \<open>vinspector \<sigma> p\<close> vinspector_def
      by blast
    have "finite v_set"
      using V_type \<open>v_set \<subseteq> V\<close> rev_finite_subset by blast

    { assume "sender m \<notin> v_set"
      have "inspector (v_set, \<sigma> \<union> {m}, p)"
        apply (rule inspector_preserved_over_message_from_non_member)
        using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close> \<open>v_set \<subseteq> V\<close> apply fastforce
        apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
        apply (simp add: \<open>sender m \<notin> v_set\<close>)
        using \<open>inspector (v_set, \<sigma>, p)\<close> by auto
    }
    hence "sender m \<notin> v_set \<Longrightarrow> inspector (v_set, \<sigma> \<union> {m}, p)" by simp
    hence "sender m \<notin> v_set \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p"
      apply (simp add: vinspector_def)
      using \<open>v_set \<subseteq> V\<close> by auto

    { assume "sender m \<in> v_set"
      have "vinspector_with \<sigma> p (\<lambda>v_set. sender m \<in> v_set \<and> finite v_set)"
        apply (simp add: vinspector_with_def)
        using \<open>finite v_set\<close> \<open>inspector (v_set, \<sigma>, p)\<close> \<open>sender m \<in> v_set\<close> by blast
      have "vinspector (\<sigma> \<union> {m}) p"
        apply (rule inspector_preserved_over_message_from_equivocating_member)
        using \<open>\<sigma> \<in> \<Sigma>\<close> apply auto[1]
        apply (simp add: \<open>\<sigma> \<in> \<Sigma>t \<and> m \<in> M\<close>)
        apply (simp add: \<open>majority_driven p\<close>)
        apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
        using \<open>sender m \<in> equivocating_validators (\<sigma> \<union> {m})\<close> apply blast
        using \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> apply blast
        by (simp add: \<open>vinspector_with \<sigma> p (\<lambda>v_set. sender m \<in> v_set \<and> finite v_set)\<close>)
    }
    hence "sender m \<in> v_set \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p" by simp

    have "vinspector (\<sigma> \<union> {m}) p"
      using \<open>sender m \<in> v_set \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p\<close> \<open>sender m \<notin> v_set \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p\<close> by blast
  }
  hence "sender m \<in> equivocating_validators (\<sigma> \<union> {m}) \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p" by simp

  show ?thesis
    using \<open>sender m \<in> equivocating_validators (\<sigma> \<union> {m}) \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p\<close> \<open>sender m \<notin> equivocating_validators (\<sigma> \<union> {m}) \<Longrightarrow> vinspector (\<sigma> \<union> {m}) p\<close> by blast
qed

(* Lemma 39: Inspector exists in all future states *)
lemma (in Protocol) inspector_preserved_in_future:
  "\<sigma> \<in> \<Sigma>t
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> vinspector \<sigma> p 
  \<Longrightarrow> (\<And>\<sigma>'. \<sigma>' \<in> futures \<sigma> \<Longrightarrow> vinspector \<sigma>' p)"
proof-
  assume "\<sigma> \<in> \<Sigma>t" "majority_driven p" "vinspector \<sigma> p"
  fix \<sigma>'
  assume "\<sigma>' \<in> futures \<sigma>"

  have "\<sigma> \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>"
    using \<open>\<sigma> \<in> \<Sigma>t\<close>
    apply (simp add: \<Sigma>t_def)
    using \<open>\<sigma>' \<in> futures \<sigma>\<close>
    apply (simp add: futures_def)
    using \<Sigma>t_is_subset_of_\<Sigma> by blast

  have "\<sigma>' \<in> \<Sigma>t"
    using \<open>\<sigma>' \<in> futures \<sigma>\<close> futures_def by blast

  obtain message_list where "MessagePath \<sigma> \<sigma>' message_list"
    using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> futures \<sigma>\<close> exist_message_path by blast

  have "\<lbrakk> MessagePath \<sigma> \<sigma>' message_list; \<sigma> \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>t; vinspector \<sigma> p \<rbrakk> \<Longrightarrow> vinspector \<sigma>' p"
    apply (induct "length message_list" arbitrary: message_list \<sigma> \<sigma>')
    apply (simp)
    using coherent_nil_message_path apply auto[1]
  proof-
    fix n message_list \<sigma> \<sigma>'
    assume "\<And>message_list \<sigma> \<sigma>'.
           n = length message_list \<Longrightarrow> MessagePath \<sigma> \<sigma>' message_list \<Longrightarrow> \<sigma> \<in> \<Sigma> \<Longrightarrow> \<sigma>' \<in> \<Sigma> \<Longrightarrow> \<sigma>' \<in> \<Sigma>t \<Longrightarrow> vinspector \<sigma> p \<Longrightarrow> vinspector \<sigma>' p"
    and "Suc n = length message_list" "MessagePath \<sigma> \<sigma>' message_list" "\<sigma> \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>t" "vinspector \<sigma> p"

    obtain m ms where "message_list = m # ms" "MessagePath (\<sigma> \<union> {m}) \<sigma>' ms" "immediately_next_message (\<sigma>,m)" "\<sigma> \<union> {m} \<in> \<Sigma>"
      by (metis \<open>MessagePath \<sigma> \<sigma>' message_list\<close> \<open>Suc n = length message_list\<close> coherent_nonnil_message_path nat.distinct(1))
    hence "\<sigma> \<in> \<Sigma>t" "\<sigma> \<union> {m} \<in> \<Sigma>t"
      apply (meson \<open>MessagePath \<sigma> \<sigma>' message_list\<close> \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> coherent_message_path_inclusive is_future_state.simps past_state_of_\<Sigma>t_is_\<Sigma>t)
      apply (meson \<open>MessagePath (\<sigma> \<union> {m}) \<sigma>' ms\<close> \<open>\<sigma> \<union> {m} \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> coherent_message_path_inclusive is_future_state.simps past_state_of_\<Sigma>t_is_\<Sigma>t)
      done
    have "vinspector (\<sigma> \<union> {m}) p"
      apply (rule inspector_preserved_over_immediately_next_message)
      using UnI2 \<open>\<sigma> \<in> \<Sigma>t\<close> \<open>\<sigma> \<union> {m} \<in> \<Sigma>\<close> message_in_state_is_valid apply auto[1]
      using \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> apply auto[1]
      apply (simp add: \<open>majority_driven p\<close>)
      apply (simp add: \<open>immediately_next_message (\<sigma>, m)\<close>)
      by (simp add: \<open>vinspector \<sigma> p\<close>)
    moreover have "n = length ms"
      using \<open>Suc n = length message_list\<close> \<open>message_list = m # ms\<close> by auto
    moreover have "MessagePath (\<sigma> \<union> {m}) \<sigma>' ms"
      using \<open>MessagePath (\<sigma> \<union> {m}) \<sigma>' ms\<close> by auto
    moreover have "\<sigma> \<union> {m} \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>"
      using \<open>\<sigma> \<union> {m} \<in> \<Sigma>\<close> apply auto[1]
      by (simp add: \<open>\<sigma>' \<in> \<Sigma>\<close>)
    moreover have "\<sigma> \<union> {m} \<in> \<Sigma>t"
      using \<open>\<sigma> \<union> {m} \<in> \<Sigma>t\<close> by auto
    ultimately show "vinspector \<sigma>' p"
      using \<open>\<And>message_list \<sigma>' \<sigma>. \<lbrakk>n = length message_list; MessagePath \<sigma> \<sigma>' message_list; \<sigma> \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>; \<sigma>' \<in> \<Sigma>t; vinspector \<sigma> p\<rbrakk> \<Longrightarrow> vinspector \<sigma>' p\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> by blast
  qed
  
  thus "vinspector \<sigma>' p"
    using \<open>MessagePath \<sigma> \<sigma>' message_list\<close> \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>t\<close> \<open>vinspector \<sigma> p\<close> by blast
qed


(* Lemma 40: Inspector is a safety oracle *)
lemma (in Protocol) inspector_is_safety_oracle :
  "\<sigma> \<in> \<Sigma>t
  \<Longrightarrow> majority_driven p
  \<Longrightarrow> vinspector \<sigma> p
  \<Longrightarrow> state_property_is_decided (naturally_corresponding_state_property p, \<sigma>)"
  apply (simp add: naturally_corresponding_state_property_def futures_def state_property_is_decided_def)
proof-
  assume s: "\<sigma> \<in> \<Sigma>t" "majority_driven p" "vinspector \<sigma> p"
  show "\<forall>x. x \<in> \<Sigma>t \<and> \<sigma> \<subseteq> x \<longrightarrow> (\<forall>x\<in>\<epsilon> x. p x)"
  proof auto
    fix x xa
    assume hyp: "xa \<in> \<epsilon> x" "x \<in> \<Sigma>t" "\<sigma> \<subseteq> x"

    show "p xa"
      apply (rule vinspector_imps_estimator_agreeing)
      apply rule
      apply (rule hyp(2))
      apply simp
      apply (simp add: \<open>majority_driven p\<close>)
      defer
      apply (simp add: hyp(1))
    proof-
      have "x \<in> futures \<sigma>"
        apply (simp add: futures_def)
        by (simp add: hyp(2) hyp(3))
      show "vinspector x p"
        apply (rule inspector_preserved_in_future)
        apply (rule s(1))
        apply (simp add: \<open>majority_driven p\<close>)
        apply (simp add: s(3))
        by (simp add: \<open>x \<in> futures \<sigma>\<close>)
    qed
  qed
qed

end
