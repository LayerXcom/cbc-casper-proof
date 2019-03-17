section \<open>Latest Message\<close>

theory LatestMessage

imports Main CBCCasper MessageJustification "Libraries/LaTeXsugar"

begin

(* ###################################################### *)
(* Section 4: Example Protocols *)
(* ###################################################### *)

(* Section 4.1:  Preliminary Definitions *)

(* Definition 4.2 *)
definition later :: "(message * message set) \<Rightarrow> message set"
  where
    "later = (\<lambda>(m, \<sigma>). {m' \<in> \<sigma>. justified m m'})"

lemma (in Protocol) later_type :
  "\<forall> \<sigma> m. \<sigma> \<in> Pow M \<and> m \<in> M \<longrightarrow> later (m, \<sigma>) \<subseteq> M"
  apply (simp add: later_def)
  by auto

lemma (in Protocol) later_type_for_state :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<longrightarrow> later (m, \<sigma>) \<subseteq> M"
  apply (simp add: later_def)
  using state_is_subset_of_M by auto

(* Definition 4.3: Messages From a Sender *)
definition from_sender :: "(validator * message set) \<Rightarrow> message set"
  where
    "from_sender = (\<lambda>(v, \<sigma>). {m \<in> \<sigma>. sender m = v})"

lemma (in Protocol) from_sender_type :
  "\<forall> \<sigma> v. \<sigma> \<in> Pow M \<and> v \<in> V \<longrightarrow> from_sender (v, \<sigma>) \<in> Pow M"
  apply (simp add: from_sender_def)
  by auto  

lemma (in Protocol) from_sender_type_for_state :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> from_sender (v, \<sigma>) \<subseteq> M"
  apply (simp add: from_sender_def)
  using state_is_subset_of_M by auto  

lemma (in Protocol) messages_from_observed_validator_is_non_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> observed \<sigma> \<longrightarrow> from_sender (v, \<sigma>) \<noteq> \<emptyset>"
  apply (simp add: observed_def from_sender_def)
  by auto

lemma (in Protocol) messages_from_validator_is_finite :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V\<sigma> \<longrightarrow> finite (from_sender (v, \<sigma>))"
  by (simp add: from_sender_def state_is_finite)

(* Definition 4.4: Message From a Group *)
definition from_group :: "(validator set * message set) \<Rightarrow> state"
  where
    "from_group = (\<lambda>(v_set, \<sigma>). {m \<in> \<sigma>. sender m \<in> v_set})"

lemma (in Protocol) from_group_type :
  "\<forall> \<sigma> v. \<sigma> \<in> Pow M \<and> v_set \<subseteq> V \<longrightarrow> from_group (v_set, \<sigma>) \<in> Pow M"
  apply (simp add: from_group_def)
  by auto

lemma (in Protocol) from_group_type_for_state :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V \<longrightarrow> from_group (v_set, \<sigma>) \<subseteq> M"
  apply (simp add: from_group_def)
  using state_is_subset_of_M by auto

(* Definition 4.5 *)
definition later_from :: "(message * validator * message set) \<Rightarrow> message set"
  where
    "later_from = (\<lambda>(m, v, \<sigma>). later (m, \<sigma>) \<inter> from_sender (v, \<sigma>))"

lemma (in Protocol) later_from_type :
  "\<forall> \<sigma> v m. \<sigma> \<in> Pow M \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_from (m, v, \<sigma>) \<in> Pow M"
  apply (simp add: later_from_def)
  using later_type from_sender_type by auto

lemma (in Protocol) later_from_type_for_state :
  "\<forall> \<sigma> v m. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_from (m, v, \<sigma>) \<subseteq> M"
  apply (simp add: later_from_def)
  using later_type_for_state from_sender_type_for_state by auto

(* Definition 4.6: Latest Messages *)
definition latest_messages :: "message set \<Rightarrow> (validator \<Rightarrow> message set)"
  where
    "latest_messages \<sigma> v = {m \<in> from_sender (v, \<sigma>). later_from (m, v, \<sigma>) = \<emptyset>}"

lemma (in Protocol) latest_messages_type :
  "\<forall> \<sigma> v. \<sigma> \<in> Pow M \<and> v \<in> V \<longrightarrow> latest_messages \<sigma> v \<in> Pow M"
  apply (simp add: latest_messages_def later_from_def)
  using from_sender_type by auto

lemma (in Protocol) latest_messages_type_for_state :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_messages \<sigma> v \<subseteq> M"
  apply (simp add: latest_messages_def later_from_def)
  using from_sender_type_for_state by auto

lemma (in Protocol) latest_messages_from_non_observed_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_messages \<sigma> v = \<emptyset>"
  by (simp add: latest_messages_def observed_def later_def from_sender_def)

(* Lemma 10: Observed non-equivocating validators have one latest message *)
definition observed_non_equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "observed_non_equivocating_validators \<sigma> = observed \<sigma> - equivocating_validators \<sigma>"

lemma (in Protocol) observed_non_equivocating_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. observed_non_equivocating_validators \<sigma> \<in> Pow V"
  apply (simp add: observed_non_equivocating_validators_def)
  using observed_type_for_state equivocating_validators_type by auto

lemma (in Protocol) justification_is_well_founded_on_messages_from_validator:
  "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> V.  wfp_on justified (from_sender (v, \<sigma>)))"
  using justification_is_well_founded_on_M from_sender_type_for_state wfp_on_subset by blast 

lemma (in Protocol) justification_is_total_on_messages_from_non_equivocating_validator:
  "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> \<longrightarrow> Relation.total_on (from_sender (v, \<sigma>)) message_justification)"
proof -
  have "\<forall> m1 m2 \<sigma> v. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<and> {m1, m2} \<subseteq> from_sender (v, \<sigma>) \<longrightarrow> sender m1 = sender m2 "
    by (simp add: from_sender_def)
  then have "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> 
      \<longrightarrow> (\<forall> m1 m2. {m1, m2} \<subseteq> from_sender (v, \<sigma>) \<longrightarrow> m1 = m2 \<or> justified m1 m2 \<or> justified m2 m1))" 
    apply (simp add: equivocating_validators_def is_equivocating_def equivocation_def from_sender_def observed_def)
    by blast
  then show ?thesis
    apply (simp add: Relation.total_on_def message_justification_def)
    using from_sender_type_for_state by blast
qed

lemma (in Protocol) justification_is_strict_linear_order_on_messages_from_non_equivocating_validator:
  "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> \<longrightarrow> strict_linear_order_on (from_sender (v, \<sigma>)) message_justification)"
  by (simp add: strict_linear_order_on_def justification_is_total_on_messages_from_non_equivocating_validator 
      irreflexivity_of_justifications transitivity_of_justifications)

(* FIXME: Use strict_well_order_on in Library/Strict_Order.thy. #84 *)
lemma (in Protocol) justification_is_strict_well_order_on_messages_from_non_equivocating_validator:
  "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> 
  \<longrightarrow> strict_linear_order_on (from_sender (v, \<sigma>)) message_justification \<and> wfp_on justified (from_sender (v, \<sigma>)))"
  using justification_is_well_founded_on_messages_from_validator
        justification_is_strict_linear_order_on_messages_from_non_equivocating_validator 
  by blast

lemma (in Protocol) latest_message_is_maximal_element_of_justification :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_messages \<sigma> v = {m. maximal_on (from_sender (v, \<sigma>)) message_justification m}"
  apply (simp add: latest_messages_def later_from_def later_def message_justification_def maximal_on_def)
  using from_sender_type_for_state apply auto
  apply (metis (no_types, lifting) IntI empty_iff from_sender_def mem_Collect_eq prod.simps(2))
  by blast  

(* Lemma 10: Observed non-equivocating validators have one latest message *)
lemma (in Protocol) observed_non_equivocating_validators_have_one_latest_message:
  "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> observed_non_equivocating_validators \<sigma>. is_singleton (latest_messages \<sigma> v))"  
  apply (simp add: observed_non_equivocating_validators_def)
proof -
  have "\<forall> \<sigma> \<in> \<Sigma>. (\<forall> v \<in> observed \<sigma> - equivocating_validators \<sigma>. is_singleton {m. maximal_on (from_sender (v, \<sigma>)) message_justification m})"
    using 
        messages_from_observed_validator_is_non_empty
        messages_from_validator_is_finite
        observed_type_for_state
        equivocating_validators_def
        justification_is_strict_linear_order_on_messages_from_non_equivocating_validator
        strict_linear_order_on_finite_non_empty_set_has_one_maximum
        maximal_and_maximum_coincide_for_strict_linear_order
    by (smt Collect_cong DiffD1 DiffD2 set_mp)
  then show "\<forall>\<sigma>\<in>\<Sigma>. \<forall>v\<in>observed \<sigma> - equivocating_validators \<sigma>. is_singleton (latest_messages \<sigma> v)"  
    using latest_message_is_maximal_element_of_justification
          observed_non_equivocating_validators_def observed_non_equivocating_validators_type 
    by fastforce
qed

(* NOTE: Lemma 5 ~ 9 and definition 4.10 are unnecessary so would be omitted. *)
(* Definition 4.7: Latest message driven estimator *)
(* TODO *)

(* Definition 4.8: Latest Estimates *)
definition latest_estimates :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates \<sigma> v = {est m | m. m \<in> latest_messages \<sigma> v}"

lemma (in Protocol) latest_estimates_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates \<sigma> v \<subseteq> C"
  using M_type Protocol.latest_messages_type_for_state Protocol_axioms latest_estimates_def by fastforce

lemma (in Protocol) latest_estimates_from_non_observed_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_estimates \<sigma> v = \<emptyset>"
  using latest_estimates_def latest_messages_from_non_observed_validator_is_empty by auto

(* Definition 4.9: Latest estimate driven estimator *)
(* TODO *)

(* Definition 4.11: Latest messages from non-Equivocating validators *)
definition latest_messages_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> message set"
  where
    "latest_messages_from_non_equivocating_validators \<sigma> v = (if is_equivocating \<sigma> v then \<emptyset> else latest_messages \<sigma> v)"

lemma (in Protocol) latest_messages_from_non_equivocating_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_messages_from_non_equivocating_validators \<sigma> v \<subseteq> M"
  by (simp add: latest_messages_type_for_state latest_messages_from_non_equivocating_validators_def)

(* Definition 4.12: Latest honest message driven estimator *)
(* TODO *)

(* Definition 4.13: Latest estimates from non-Equivocating validators *)
definition latest_estimates_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_non_equivocating_validators \<sigma> v = {est m | m. m \<in> latest_messages_from_non_equivocating_validators \<sigma> v}"

lemma (in Protocol) latest_estimates_from_non_equivocating_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates_from_non_equivocating_validators \<sigma> v \<in> Pow C"
  using Protocol.latest_estimates_type Protocol_axioms latest_estimates_def latest_estimates_from_non_equivocating_validators_def latest_messages_from_non_equivocating_validators_def by auto

lemma (in Protocol) latest_estimates_from_non_equivocating_validators_from_non_observed_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_estimates_from_non_equivocating_validators \<sigma> v = \<emptyset>"
  by (simp add: latest_estimates_from_non_equivocating_validators_def latest_messages_from_non_equivocating_validators_def latest_messages_from_non_observed_validator_is_empty)

(* Definition 4.14: Latest honest estimate driven estimator *)
(* TODO *)

end
