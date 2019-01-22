theory ExampleProtocols

imports Main CBCCasper

begin

(* Section 4: Example Protocols *)
(* Section 4.1:  Preliminary Definitions *)

(* Definition 4.1: Observed validators *)
definition observed :: "state \<Rightarrow> validator set"
  where
    "observed \<sigma> = {sender m | m . m \<in> \<sigma>}"

(* Definition 4.2 *)
fun later :: "(message * state) \<Rightarrow> state"
  where
    "later (m, \<sigma>) = {m'. m' \<in> \<sigma> \<and>  m \<in> justification m'}"

(* Definition 4.3: Messages From a Sender *)
fun from_sender :: "(validator * state) \<Rightarrow> state"
  where
    "from_sender (v, \<sigma>) = {m. m \<in> \<sigma> \<and> sender m = v}"

(* Definition 4.4: Message From a Group *)
fun from_group :: "(validator set * state) \<Rightarrow> state"
  where
    "from_group (v_set, \<sigma>) = {m. m \<in> \<sigma> \<and> sender m \<in> v_set}"

(* Definition 4.5 *)
fun later_from :: "(message * validator * state) \<Rightarrow> state"
  where
    "later_from (m, v, \<sigma>) = later (m, \<sigma>) \<inter> from_sender (v, \<sigma>)"

(* Definition 4.6: Latest Message *)
definition latest_message :: "state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_message \<sigma> v = {m. m \<in> from_sender (v, \<sigma>) \<and> later_from (m, v, \<sigma>) = \<emptyset>}"

(* Definition 4.7: Latest message driven estimator *)
(* TODO *)

(* Definition 4.8: Latest Estimates *)
definition latest_estimates :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates \<sigma> v = {est m | m. m \<in> latest_message \<sigma> v}"

(* Definition 4.9: Latest estimate driven estimator *)
(* TODO *)

(* Lemma 5: Non-equivocating validators have at most one latest message *)
lemma non_equivocating_validators_have_at_most_one_latest_message:
  "\<forall> params v. v \<in> V params \<and> v \<notin> equivocating_validators \<sigma> \<Longrightarrow> card (latest_message \<sigma> v) \<le> 1"
  using V.simps by blast

(* Definition 4.10 *)
(* TODO *)

(* Lemma 6 *)
(* TODO *)

(* Lemma 7 *)
(* TODO *)

(* Lemma 8 *)
(* TODO *)

(* Lemma 9 *)
(* TODO *)

(* Lemma 10 *)
(* TODO *)

(* Definition 4.11: Latest messages from non-Equivocating validators *)
definition latest_messages_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> message set"
  where
    "latest_messages_from_non_equivocating_validators \<sigma> v = (if v \<in> equivocating_validators \<sigma> then \<emptyset> else latest_message \<sigma> v)"

(* Definition 4.12: Latest honest message driven estimator *)
(* TODO *)

(* Definition 4.13: Latest estimates from non-Equivocating validators *)
definition latest_estimates_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_non_equivocating_validators \<sigma> v = {est m | m. m \<in> latest_messages_from_non_equivocating_validators \<sigma> v}"

(* Definition 4.14: Latest honest estimate dricen estimator *)
(* TODO *)

end
