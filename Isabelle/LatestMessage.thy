theory LatestMessage

imports Main CBCCasper

begin

(* ###################################################### *)
(* Section 4: Example Protocols *)
(* ###################################################### *)

(* Section 4.1:  Preliminary Definitions *)

(* Definition 4.2 *)
definition later :: "(message * state) \<Rightarrow> message set"
  where
    "later = (\<lambda>(m, \<sigma>). {m' \<in> \<sigma>. justified m m'})"

lemma (in Protocol) later_type :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<longrightarrow> later (m, \<sigma>) \<subseteq> M"
  apply (simp add: later_def)
  using state_is_subset_of_M by auto

(* Definition 4.3: Messages From a Sender *)
definition from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender  = (\<lambda>(v, \<sigma>). {m \<in> \<sigma>. sender m = v})"

lemma (in Protocol) from_sender_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> from_sender (v, \<sigma>) \<subseteq> M"
  apply (simp add: from_sender_def)
  using state_is_subset_of_M by auto  

(* Definition 4.4: Message From a Group *)
definition from_group :: "(validator set * state) \<Rightarrow> state"
  where
    "from_group = (\<lambda>(v_set, \<sigma>). {m \<in> \<sigma>. sender m \<in> v_set})"

lemma (in Protocol) from_group_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V \<longrightarrow> from_group (v_set, \<sigma>) \<subseteq> M"
  apply (simp add: from_group_def)
  using state_is_subset_of_M by auto

(* Definition 4.5 *)
definition later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from = (\<lambda>(m, v, \<sigma>). later (m, \<sigma>) \<inter> from_sender (v, \<sigma>))"

lemma (in Protocol) later_from_type :
  "\<forall> \<sigma> v m. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_from (m, v, \<sigma>) \<subseteq> M"
  apply (simp add: later_from_def)
  using later_type from_sender_type by auto

(* Definition 4.6: Latest Messages *)
definition latest_messages :: "state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_messages \<sigma> v = {m \<in> from_sender (v, \<sigma>). later_from (m, v, \<sigma>) = \<emptyset>}"

lemma (in Protocol) latest_messages_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_messages \<sigma> v \<subseteq> M"
  apply (simp add: latest_messages_def later_from_def)
  using from_sender_type by auto

lemma (in Protocol) latest_messages_from_non_observed_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_messages \<sigma> v = \<emptyset>"
  by (simp add: latest_messages_def observed_def later_def from_sender_def)

(* Definition 4.7: Latest message driven estimator *)
(* TODO *)

(* Definition 4.8: Latest Estimates *)
definition latest_estimates :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates \<sigma> v = {est m | m. m \<in> latest_messages \<sigma> v}"

lemma (in Protocol) latest_estimates_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates \<sigma> v \<subseteq> C"
  using M_type Protocol.latest_messages_type Protocol_axioms latest_estimates_def by fastforce

lemma (in Protocol) latest_estimates_from_non_observed_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_estimates \<sigma> v = \<emptyset>"
  using latest_estimates_def latest_messages_from_non_observed_validator_is_empty by auto

(* Definition 4.9: Latest estimate driven estimator *)
(* TODO *)

(* Lemma 10: Observed non-equivocating validators have one latest message *)
fun observed_non_equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "observed_non_equivocating_validators \<sigma> = observed \<sigma> - equivocating_validators \<sigma>"

lemma (in Protocol) observed_non_equivocating_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. observed_non_equivocating_validators \<sigma> \<subseteq> V"
  using observed_type equivocating_validators_type by auto


(* TODO #78: Justification is well-ordered over messages from a non-equivocating validator *)
lemma (in Protocol) justification_is_well_founded_on_messages_from_non_equivocating_validator:
  "\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> \<longrightarrow> wfp_on justified (from_sender (v, \<sigma>))"
  oops

lemma (in Protocol) justification_is_total_order_on_messages_from_non_equivocating_validator:
  "\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> \<longrightarrow> total_on justified (from_sender (v, \<sigma>))"
  oops


(* TODO #59 *)
lemma (in Protocol) observed_non_equivocating_validators_have_one_latest_message:
  "\<forall> v \<in> observed_non_equivocating_validators \<sigma>. card (latest_message \<sigma> v) = 1"
  oops

(* NOTE: Lemma 5 ~ 9 and definition 4.10 are unnecessary so would be omitted. *)
(* Lemma 5: Non-equivocating validators have at most one latest message *)
lemma (in Protocol) non_equivocating_validators_have_at_most_one_latest_message:
  "\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> \<longrightarrow> card (latest_message \<sigma> v) \<le> 1"
  oops

(* Definition 4.10: The relation \<succeq> (Comparison of cardinalities of justification)*)
(* Lemma 6 *)

(* Lemma 7 *)
lemma (in Protocol) monotonicity_of_justifications :
  "\<forall> m m' \<sigma>. m \<in> M \<and> \<sigma> \<in> \<Sigma> \<and> m' \<in> later (m, \<sigma>) \<longrightarrow> justification m \<subseteq> justification m'"
  apply (simp add: later_def)
  by (meson M_type justified_def message_in_state_is_valid state_is_in_pow_M_i)

(* Lemma 8 *)
(* Lemma 9 *)

(* Definition 4.11: Latest messages from non-Equivocating validators *)
definition latest_messages_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> message set"
  where
    "latest_messages_from_non_equivocating_validators \<sigma> v = (if is_equivocating \<sigma> v then \<emptyset> else latest_messages \<sigma> v)"

lemma (in Protocol) latest_messages_from_non_equivocating_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_messages_from_non_equivocating_validators \<sigma> v \<subseteq> M"
  by (simp add: latest_messages_type latest_messages_from_non_equivocating_validators_def)

(* Definition 4.12: Latest honest message driven estimator *)
(* TODO *)

(* Definition 4.13: Latest estimates from non-Equivocating validators *)
definition latest_estimates_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_non_equivocating_validators \<sigma> v = {est m | m. m \<in> latest_messages_from_non_equivocating_validators \<sigma> v}"

lemma (in Protocol) latest_estimates_from_non_equivocating_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates_from_non_equivocating_validators \<sigma> v \<subseteq> C"
  using Protocol.latest_estimates_type Protocol_axioms latest_estimates_def latest_estimates_from_non_equivocating_validators_def latest_messages_from_non_equivocating_validators_def by auto

lemma (in Protocol) latest_estimates_from_non_equivocating_validators_from_non_observed_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_estimates_from_non_equivocating_validators \<sigma> v = \<emptyset>"
  by (simp add: latest_estimates_from_non_equivocating_validators_def latest_messages_from_non_equivocating_validators_def latest_messages_from_non_observed_validator_is_empty)

(* Definition 4.14: Latest honest estimate driven estimator *)
(* TODO *)

end
