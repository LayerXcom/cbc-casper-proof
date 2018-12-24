theory Casper

imports Main

begin

(* Section 2: Description of CBC Casper *)
(* Section 2.1: CBC Casper "Parameters" *)

(* Definition 2.1 *)
datatype validator = Validator int

(* Definition 2.2 *)
type_synonym weight = "validator \<Rightarrow> int"

(* Definition 2.3 *)
type_synonym threshold = int

(* Definition 2.4 *)
datatype consensus_value = Consensus_value int

(* NOTE: list is used here because set can not be used for recursive definition. *)
datatype message =
  Message "consensus_value * validator * message list"

type_synonym state = "message set"

(* Definition 2.5 *)
(* NOTE: Here estimator returns only one value, avoiding non-determinism. 
Also, estimator is parameterized by weight. *)
type_synonym estimator = "weight \<Rightarrow> state \<Rightarrow> consensus_value"


(* Section 2.2: Protocol Definition *)

(* Definition 2.6 *)
fun sender :: "message \<Rightarrow> validator"
  where
    "sender (Message (_, v, _)) = v"

fun est :: "message \<Rightarrow> consensus_value"
  where
     "est (Message (c, _, _)) = c"

fun justification :: "message \<Rightarrow> state"
  where
    "justification (Message (_, _, ml)) = set ml"

(* Definition 2.7 *)
fun is_valid :: "weight \<Rightarrow>(estimator \<Rightarrow> (message \<Rightarrow> bool))"
  where
    "is_valid w e (Message (c, v, s)) = (c = e w (set s))"

(* FIXME: Can we construct valid_message type? Currently we assume all states are valid in all the 
"definition"s and use is_valid_state for all occurrences of state type in lemmas. *)
definition is_valid_state :: "weight \<Rightarrow> estimator \<Rightarrow> state \<Rightarrow> bool"
  where
    "is_valid_state w e s = (\<forall> m \<in> s. is_valid w e m)"

(* Definition 2.8: Protocol state transitions \<rightarrow> *)
definition is_future_state :: "state \<Rightarrow> state \<Rightarrow> bool"
  where
    "is_future_state s1 s2 = (s1 \<supseteq> s2)"

(* Definition 2.9 *)
definition equivocation :: "message \<Rightarrow> message \<Rightarrow> bool"
  where
    "equivocation m1 m2 =
      (sender m1 = sender m2 \<and> m1 \<noteq> m2 \<and> m1 \<notin> justification(m2) \<and> m2 \<notin> justification(m1))"

(* Definition 2.10 *)
definition equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators s = 
      {v. \<exists> m1 m2. m1 \<in> s \<and> m2 \<in> s \<and> equivocation m1 m2 \<and> sender m1 = v}"

(* Definition 2.11 *)
definition equivocation_fault_weight :: "weight \<Rightarrow> state \<Rightarrow> int"
  where
    "equivocation_fault_weight w s = sum w (equivocating_validators s)"

(* Definition 2.12 *)
definition is_faults_lt_threshold :: "threshold \<Rightarrow> weight \<Rightarrow> state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold t w s = (equivocation_fault_weight w s < t)"

(* Section 3: Safety Proof *)
(* Section 3.1: Guaranteeing Common Futures *)

(* Definition 3.1 *)
definition futures :: "threshold \<Rightarrow> weight \<Rightarrow> state \<Rightarrow> state set"
  where
    "futures t w s = {s'. is_faults_lt_threshold t w s' \<and> is_future_state s' s}"

(* Lemma 1 *)
lemma monotonic_futures :
  "\<forall> s' s. is_faults_lt_threshold t w s' \<and> is_faults_lt_threshold t w s
   \<and> is_valid_state w e s' \<and> is_valid_state w e s
   \<Longrightarrow> (s' \<in> futures t w s \<longleftrightarrow> futures t w s' \<subseteq> futures t w s)"
   using futures_def is_future_state_def by auto

notation Set.empty ("\<emptyset> ")

(* Theorem 1 *)
theorem two_party_common_futures :
  "\<forall> s1 s2. is_faults_lt_threshold t w s1 \<and> is_faults_lt_threshold t w s2
   \<and> is_valid_state w e s1 \<and> is_valid_state w e s2
  \<Longrightarrow> is_faults_lt_threshold t w (s1 \<union> s2)
  \<Longrightarrow> futures t w s1 \<inter> futures t w s2 \<noteq> \<emptyset>"
  using futures_def is_future_state_def by auto

(* Theorem 2 *)
theorem n_party_common_futures :
  "\<forall> s_set. \<forall> s. s \<in> s_set \<and> is_faults_lt_threshold t w s \<and> is_valid_state w e s
  \<Longrightarrow> is_faults_lt_threshold t w (\<Union> s_set)
  \<Longrightarrow> futures t w s1 \<inter> futures t w s2 \<noteq> \<emptyset>"
  by blast


end
