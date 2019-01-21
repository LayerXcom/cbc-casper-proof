theory ExampleProtocols

imports Main CBCCasper

begin

(* Section 4: Example Protocols *)
(* Section 4.1:  Preliminary Definitions *)

(* Definition 4.1: Observed validators *)
definition observed :: "state \<Rightarrow> validator set"
  where
    "observed \<sigma> = {sender m | m. m \<in> \<sigma>}"

(* Definition 4.2 *)
fun later :: "params \<Rightarrow> (message * state) \<Rightarrow> state"
  where
    "later params (m, \<sigma>) = {m' \<in> M params. m' \<in> \<sigma> \<and>  m \<in> justification m'}"

(* Definition 4.3: Messages From a Sender *)
fun from_sender :: "params \<Rightarrow> (validator * state) \<Rightarrow> state"
  where
    "from_sender params (v, \<sigma>) = {m \<in> M params. m \<in> \<sigma> \<and> sender m = v}"

(* Definition 4.4: Message From a Group *)
fun from_group :: "params \<Rightarrow> (validator set * state) \<Rightarrow> state"
  where
    "from_group params (v_set, \<sigma>) = {m \<in> M params. m \<in> \<sigma> \<and> sender m \<in> v_set}"

(* Definition 4.5 *)
fun later_from :: "params \<Rightarrow> (message * validator * state) \<Rightarrow> state"
  where
    "later_from params (m, v, \<sigma>) = later params (m, \<sigma>) \<inter> from_sender params (v, \<sigma>)"

(* Definition 4.6: Latest Message *)
definition latest_message :: "params \<Rightarrow> state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_message params \<sigma> v = {m \<in> M params. m \<in> from_sender params (v, \<sigma>) \<and> later_from params (m, v, \<sigma>) = \<emptyset>}"

(* Definition 4.7: Latest message driven estimator *)
(* TODO *)

(* Definition 4.8: Latest Estimates *)
definition latest_estimates :: "params \<Rightarrow> state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates params \<sigma> v = {est m | m. m \<in> M params \<and> m \<in> latest_message params \<sigma> v}"

(* Definition 4.9: Latest estimate driven estimator *)
(* TODO *)

(* Lemma 5: Non-equivocating validators have at most one latest message *)
lemma non_equivocating_validators_have_at_most_one_latest_message:
  "\<forall> params \<sigma> v. is_valid_params params \<and> \<sigma> \<in> \<Sigma> params \<and> v \<in> V params
   \<longrightarrow> v \<notin> equivocating_validators params \<sigma>
   \<longrightarrow> card (latest_message params \<sigma> v) \<le> 1"
  (* TODO *)
  (* using V.simps by blast *)
  oops
end
