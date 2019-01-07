theory ExampleProtocols

imports Main ConsensusSafety

begin

(* Section 4: Example Protocols *)
(* Section 4.1 *)

(* Definition 4.1 Observed validators *)
definition observed :: "state \<Rightarrow> validator set"
  where
    (* "observed s = {v. \<exists> m. v = sender m \<and> m \<in> s}" *)
    "observed s = {sender m |m . m \<in> s}"

(* Definition 4.2 *)
fun later :: "(message * state) \<Rightarrow> state"
  where
    "later (m, s) = {m'. m' \<in> s \<and> m \<in> justification m'}"

(* Definition 4.3 Messages From a Sender *)
fun from_sender :: "(validator * state) \<Rightarrow> state"
  where
    "from_sender (v, s) = {m. m \<in> s \<and> sender m = v}"

(* Definition 4.4 Message From a Group *)
fun from_group :: "(validator set * state) \<Rightarrow> state"
  where
    "from_group (V, s) = {m. m \<in> s \<and> sender m \<in> V}"

(* Definition 4.5 *)
fun later_from :: "(message * validator * state) \<Rightarrow> state"
  where
    "later_from (m, v, s) = later (m, s) \<inter> from_sender (v, s)"

(* Definition 4.6 Latest Message *)
definition latest_message :: "state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_message s v = {m. m \<in> from_sender (v, s) \<and> later_from (m, v, s) = \<emptyset>}"

(* Definition 4.7 Latest message driven estimator *)
(* TODO *)

(* Definition 4.8 Latest Estimates *)
definition latest_estimates :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates s v = {est(m) | m. m \<in> latest_message s v}"

(* Definition 4.9 Latest estimate driven estimator *)
(* TODO *)

(* Lemma 5 Non-equivocating validators have at most one latest message *)
(* TODO *)

(*
lemma non_equivocating_validators_have_at_most_one_latest_message:
  (* "\<forall> v \<in> V. v \<notin> equivocating_validators s \<Longrightarrow> count (latest_estimates s v) \<le> 1" *)
  (* prove the contrapositive *)
  "\<forall> v \<in> V. count (latest_estimates s v) > 1 \<Longrightarrow> v \<in> equivocating_validators s" 
  apply (simp add: latest_estimates_def latest_message_def)
*)

end
