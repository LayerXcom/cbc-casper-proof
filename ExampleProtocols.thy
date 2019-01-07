theory ExampleProtocols

imports Main ConsensusSafety

begin

(* Section 4: Example Protocols *)
(* Section 4.1 *)

(* Definition 4.1 *)
definition observed :: "state \<Rightarrow> validator set"
  where
    (* "observed s = {v. \<exists> m. v = sender m \<and> m \<in> s}" *)
    "observed s = {sender m |m . m \<in> s}"

(* Definition 4.2 *)
fun later :: "(message * state) \<Rightarrow> state"
  where
    "later (m, s) = {m'. m' \<in> s \<and> m \<in> justification m'}"

(* Definition 4.3 *)
fun from_sender :: "(validator * state) \<Rightarrow> state"
  where
    "from_sender (v, s) = {m. m \<in> s \<and> sender m = v}"

(* Definition 4.4 *)
fun from_group :: "(validator set * state) \<Rightarrow> state"
  where
    "from_group (V, s) = {m. m \<in> s \<and> sender m \<in> V}"

(* Definition 4.5 *)
fun later_from :: "(message * validator * state) \<Rightarrow> state"
  where
    "later_from (m, v, s) = later (m, s) \<inter> from_sender (v, s)"

(* Definition 4.6 *)
definition latest_message :: "state \<Rightarrow> (validator \<Rightarrow> state)"
  where
    "latest_message s v = {m. m \<in> from_sender (v, s) \<and> later_from (m, v, s) = \<emptyset>}"

end