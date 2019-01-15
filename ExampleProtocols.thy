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
fun message_order
  where
    "message_order (m1, m2) = (card (justification m1) \<ge> card (justification m2))"

(* Lemma 6 *)
(* TODO *)

(* Lemma 7 *)       
lemma monotonicity_of_justifications:
  "\<forall> params \<sigma>' \<sigma>. is_valid_params params \<and> \<sigma>' \<in> \<Sigma> params \<and> \<sigma> \<in> \<Sigma> params \<Longrightarrow>
  m' \<in> later (m, \<sigma>) \<Longrightarrow> justification m  \<subseteq> justification m'"
  by (meson V.simps is_valid_params_def is_valid_validators_def)

(* Lemma 8 *)       
lemma the_minimal_elements_are_the_latest_messages:
  "\<forall> params \<sigma>' \<sigma>. is_valid_params params \<and> \<sigma>' \<in> \<Sigma> params \<and> \<sigma> \<in> \<Sigma> params \<Longrightarrow>
  \<forall>m'. m' \<in> from_sender (v, \<sigma>) \<and> message_order (m, m')\<Longrightarrow>                   
  m \<in> latest_message \<sigma> v"
  apply (rule, rule, rule)
proof -
  fix params
  assume hyp: "is_valid_params params"
  assume "\<forall>m'. m' \<in> from_sender (v, \<sigma>) \<and> message_order (m, m') \<Longrightarrow>  m \<notin> latest_message \<sigma> v"

  have
    "  \<forall>m'. m' \<in> from_sender (v, \<sigma>) \<and> message_order (m, m') \<and> \<not> (m \<in> latest_message \<sigma> v) \<Longrightarrow>
    \<forall>m'. \<exists> ms. m' \<in> from_sender (v, \<sigma>) \<and> message_order (m, m') \<and> ms \<in> later_from (m, v, \<sigma>)"
    apply (simp add: latest_message_def)                                 
    by auto

  oops

(* Lemma 10 *)
lemma observed_non_equivocating_validators_have_one_latest_message:
  "\<forall> params \<sigma> v. is_valid_params params \<and> \<sigma> \<in> \<Sigma> params \<and> v \<in> V params \<Longrightarrow>
  v \<in> observed \<sigma> \<and> v \<notin> equivocating_validators \<sigma> \<Longrightarrow> 
  card(latest_message \<sigma> v) == 1"
  apply (simp add: equivocating_validators_def latest_message_def)
  sorry
end