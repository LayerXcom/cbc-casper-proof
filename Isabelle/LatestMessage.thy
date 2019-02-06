theory LatestMessage

imports Main CBCCasper

begin

(* Section 4: Example Protocols *)
(* Section 4.1:  Preliminary Definitions *)

(* Definition 4.2 *)
fun later :: "(message * state) \<Rightarrow> message set"
  where
    "later (m, \<sigma>) = {m' \<in> \<sigma>. justified m m'}"

lemma (in Protocol) later_type :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> M \<longrightarrow> later (m, \<sigma>) \<subseteq> M"
  using state_is_subset_of_M by auto

(* Definition 4.3: Messages From a Sender *)
fun  from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender (v, \<sigma>) = {m \<in> \<sigma>. sender m = v}"

lemma (in Protocol) from_sender_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> from_sender (v, \<sigma>) \<subseteq> M"
  using state_is_subset_of_M by auto  

(* Definition 4.4: Message From a Group *)
fun from_group :: "(validator set * state) \<Rightarrow> state"
  where
    "from_group (v_set, \<sigma>) = {m \<in> \<sigma>. sender m \<in> v_set}"

lemma (in Protocol) from_group_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v_set \<subseteq> V \<longrightarrow> from_group (v_set, \<sigma>) \<subseteq> M"
  using state_is_subset_of_M by auto

(* Definition 4.5 *)
fun later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = later (m, \<sigma>) \<inter> from_sender (v, \<sigma>)"

lemma (in Protocol) later_from_type :
  "\<forall> \<sigma> v m. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_from (m, v, \<sigma>) \<subseteq> M"
  using later_type from_sender_type by auto

(* Definition 4.6: Latest Messages *)
definition latest_messages :: "state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_messages \<sigma> v = {m \<in> from_sender (v, \<sigma>). later_from (m, v, \<sigma>) = \<emptyset>}"

lemma (in Protocol) latest_messages_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_messages \<sigma> v \<subseteq> M"
  using latest_messages_def state_is_subset_of_M by auto

lemma (in Protocol) latest_messages_from_silent_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_messages \<sigma> v = \<emptyset>"
  by (simp add: latest_messages_def observed_def)

(* Definition 4.7: Latest message driven estimator *)
(* TODO *)

(* Definition 4.8: Latest Estimates *)
definition latest_estimates :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates \<sigma> v = {est m | m. m \<in> latest_messages \<sigma> v}"

lemma (in Protocol) latest_estimates_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates \<sigma> v \<subseteq> C"
  using M_type Protocol.latest_messages_type Protocol_axioms latest_estimates_def by fastforce

lemma (in Protocol) latest_estimates_from_silent_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_estimates \<sigma> v = \<emptyset>"
  using latest_estimates_def latest_messages_from_silent_validator_is_empty by auto

(* Definition 4.9: Latest estimate driven estimator *)
(* TODO *)

(* Lemma 5: Non-equivocating validators have at most one latest message *)
lemma (in Protocol) non_equivocating_validators_have_at_most_one_latest_message:
  "\<forall> v \<in> V. v \<notin> equivocating_validators \<sigma> \<longrightarrow> card (latest_message \<sigma> v) \<le> 1"
  oops

(* Definition 4.10 *)
(* TODO *)

(* Lemma 6 *)
(* TODO *)

(* Lemma 7 *)
lemma (in Protocol) monotonicity_of_justifications :
  "\<forall> m m' \<sigma>. m \<in> M \<and> \<sigma> \<in> \<Sigma> \<and> m' \<in> later (m, \<sigma>) \<longrightarrow> justification m \<subseteq> justification m'"
  apply simp
  by (meson M_type justified_def message_in_state_is_valid state_is_in_pow_M_i)

(* Lemma 8 *)
(* TODO *)

(* Lemma 9 *)
(* TODO *)

(* Lemma 10 *)
(* TODO *)

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

lemma (in Protocol) latest_estimates_from_non_equivocating_validators_from_silent_validator_is_empty :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> v \<notin> observed \<sigma> \<longrightarrow> latest_estimates_from_non_equivocating_validators \<sigma> v = \<emptyset>"
  by (simp add: latest_estimates_from_non_equivocating_validators_def latest_messages_from_non_equivocating_validators_def latest_messages_from_silent_validator_is_empty)

(* Definition 4.14: Latest honest estimate driven estimator *)
(* TODO *)

end
