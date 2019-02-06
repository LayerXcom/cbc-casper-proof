theory LatestMessage

imports Main CBCCasper

begin

(* Section 4: Example Protocols *)
(* Section 4.1:  Preliminary Definitions *)

(* Definition 4.1: Observed validators *)
(* NOTE: m \<in> M *)
definition (in Protocol) observed :: "state \<Rightarrow> validator set"
  where
    "observed \<sigma> = {sender m | m. m \<in> \<sigma>}"

lemma (in Protocol) oberved_type :
  "\<forall> \<sigma> \<in> \<Sigma>. observed \<sigma> \<subseteq> V"
  using Protocol.M_type Protocol_axioms observed_def state_is_subset_of_M by fastforce

(* Definition 4.2 *)
fun (in Protocol) later :: "(message * state) \<Rightarrow> state"
  where
    "later (m, \<sigma>) = {m' \<in> M. m' \<in> \<sigma> \<and>  m \<in> justification m'}"

(* Definition 4.3: Messages From a Sender *)
fun (in Protocol) from_sender :: "(validator * state) \<Rightarrow> state"
  where
    "from_sender (v, \<sigma>) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v}"

(* Definition 4.4: Message From a Group *)
fun (in Protocol) from_group :: "(validator set * state) \<Rightarrow> state"
  where
    "from_group (v_set, \<sigma>) = {m \<in> M. m \<in> \<sigma> \<and> sender m \<in> v_set}"

(* Definition 4.5 *)
fun (in Protocol) later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = {m \<in> M. m \<in> later (m, \<sigma>) \<inter> from_sender (v, \<sigma>)}"

(* Definition 4.6: Latest Message *)
definition (in Protocol) latest_message :: "state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_message \<sigma> v = {m \<in> M. m \<in> from_sender (v, \<sigma>) \<and> later_from (m, v, \<sigma>) = \<emptyset>}"

(* Definition 4.7: Latest message driven estimator *)
(* TODO *)

(* Definition 4.8: Latest Estimates *)
definition (in Protocol) latest_estimates :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates \<sigma> v = {est m | m. m \<in> latest_message \<sigma> v}"

lemma (in Protocol) latest_estimates_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates \<sigma> v \<subseteq> C"
  using M_type latest_estimates_def latest_message_def by auto

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
  using M_type state_is_in_pow_M_i by auto

(* Lemma 8 *)
(* TODO *)

(* Lemma 9 *)
(* TODO *)

(* Lemma 10 *)
(* TODO *)

(* Definition 4.11: Latest messages from non-Equivocating validators *)
definition  (in Protocol) latest_messages_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> message set"
  where
    "latest_messages_from_non_equivocating_validators \<sigma> v = (if v \<in> equivocating_validators \<sigma> then \<emptyset> else latest_message \<sigma> v)"

(* Definition 4.12: Latest honest message driven estimator *)
(* TODO *)

(* Definition 4.13: Latest estimates from non-Equivocating validators *)
definition (in Protocol) latest_estimates_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_non_equivocating_validators \<sigma> v = {est m | m. m \<in> M \<and> m \<in> latest_messages_from_non_equivocating_validators \<sigma> v}"

(* Definition 4.14: Latest honest estimate driven estimator *)
(* TODO *)

end
