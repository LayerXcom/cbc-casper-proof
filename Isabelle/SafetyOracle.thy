theory SafetyOracle

imports Main CBCCasper ConsensusSafety LatestMessage

begin

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* NOTE: Definition 7.1 is replaced by definition 4.2*)
(* NOTE: Definition 7.2 is duplicate of definition 4.3 *)
(* NOTE: Definition 7.3 is duplicate of definition 4.5 *)
(* NOTE: Definition 7.4 is duplicate of definition 4.6 *)
(* NOTE: Definition 7.5 is duplicate of definition 4.11 *)
(* NOTE: Definition 7.6 is duplicate of definition 4.13 *)

(* Definition 7.7 *)
fun latest_justifications_from_non_equivocating_validators :: "state \<Rightarrow> validator \<Rightarrow> state set"
  where
    "latest_justifications_from_non_equivocating_validators \<sigma> v = 
      {justification m | m. m \<in> latest_messages_from_non_equivocating_validators \<sigma> v}"

lemma (in Protocol) latest_justifications_from_non_equivocating_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_justifications_from_non_equivocating_validators \<sigma> v \<subseteq> \<Sigma>"
  using M_type latest_messages_from_non_equivocating_validators_type by auto

(* Definition 7.8 *)
(* NOTE: Modified from the original draft. *)
fun observed_non_equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "observed_non_equivocating_validators \<sigma> = observed \<sigma> - equivocating_validators \<sigma>"

fun  agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators (p, \<sigma>) = {v \<in> observed_non_equivocating_validators \<sigma>. \<forall> c \<in> latest_estimates_from_non_equivocating_validators \<sigma> v. p c}"

lemma (in Protocol) agreeing_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (p, \<sigma>) \<subseteq> V"
  using oberved_type by auto

(* Definition 7.9 *)
fun disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators (p, \<sigma>) = {v \<in> observed_non_equivocating_validators \<sigma>. \<exists> c \<in> latest_estimates_from_non_equivocating_validators \<sigma> v. \<not> p c}"

lemma (in Protocol) disagreeing_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. disagreeing_validators (p, \<sigma>) \<subseteq> V"
  using oberved_type by auto

(* Definition 7.10 *)
definition (in Params) weight_measure :: "validator set \<Rightarrow> real"
  where
    "weight_measure v_set = sum W v_set"

(* Definition 7.11 *)
fun (in Params) is_majority :: "(validator set * state) \<Rightarrow> bool"
  where
    "is_majority (v_set, \<sigma>) = (weight_measure v_set > (weight_measure V - weight_measure (equivocating_validators \<sigma>)) div 2)"
   
(* Definition 7.12 *)
definition (in AbstractProtocol) is_majority_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven p = (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> is_majority (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>. p c))"

(* Definition 7.13 *)
definition (in AbstractProtocol) is_max_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven p =
      (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (disagreeing_validators (p, \<sigma>)) \<longrightarrow> c \<in> \<epsilon> \<sigma> \<and> p c)"

(* Definition 7.14 *)
fun later_disagreeing_messages :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_messages (p, m, v, \<sigma>) = {m' \<in> later_from (m, v, \<sigma>). \<not> p (est m')}"

lemma (in Protocol) later_disagreeing_messages_type :
  "\<forall> p \<sigma> v m. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<and> m \<in> M \<longrightarrow> later_disagreeing_messages (p, m, v, \<sigma>) \<subseteq> M"
  using later_from_type by auto

(* Definition 7.15 *)
(* `the_elem` is built-in  *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)
fun is_clique :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique (v_set, p, \<sigma>) = 
     (\<forall> v \<in> v_set. v_set \<subseteq> agreeing_validators (p, the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v))
     \<and>  (\<forall>  v' \<in> v_set. later_disagreeing_messages (p, the_elem (latest_messages_from_non_equivocating_validators (the_elem (latest_justifications_from_non_equivocating_validators \<sigma> v)) v'), v', \<sigma>) = \<emptyset>))"


(* Section 7.3: Cliques Survive Messages from Validators Outside Clique *)

(* Definition 7.17 *)
abbreviation (in Params) minimal_transitions :: "(state * state) set"
  where
    "minimal_transitions \<equiv> {(\<sigma>, \<sigma>') | \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t \<and> is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>'
      \<and> (\<nexists> \<sigma>''. \<sigma>'' \<in> \<Sigma> \<and> is_future_state (\<sigma>'', \<sigma>) \<and> is_future_state (\<sigma>', \<sigma>'') \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>'' \<noteq> \<sigma>')}"

(* A minimal transition corresponds to receiving a single new message with justification drawn from the initial
protocol state *)
lemma (in Protocol) minimal_transition_implies_recieving_a_single_message :
  "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t \<and> \<sigma>' \<in> \<Sigma>t
  \<longrightarrow> (\<sigma>, \<sigma>') \<in> minimal_transitions  \<longrightarrow> is_singleton (\<sigma>'- \<sigma>)"
  oops

(* Lemma 11: Minimal transitions do not change Later_From for any non-sender *)
lemma (in Protocol) later_from_not_affected_by_minimal_transitions :
  "\<forall> \<sigma> \<sigma>' m m'. (\<sigma>, \<sigma>') \<in> minimal_transitions \<and> m' = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> (\<forall> v \<in> V - {sender m'}. later_from (m, v, \<sigma>) = later_from (m, v, \<sigma>'))"
  oops

(* Definition 7.18: One layer clique oracle threshold size *) 
fun (in Params) gt_threshold :: "(validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold (v_set, \<sigma>)
       = (weight_measure v_set > (weight_measure v_set) div 2 + t  - weight_measure (equivocating_validators \<sigma>))"

(* Definition 7.19: Clique oracle with 1 layers *)
fun (in Params) is_clique_oracle :: "(validator set * state * consensus_value_property) \<Rightarrow> bool"
  where
    "is_clique_oracle (v_set, \<sigma>, p)
       = (is_clique (v_set - (equivocating_validators \<sigma>), p, \<sigma>) \<and> gt_threshold (v_set - (equivocating_validators \<sigma>), \<sigma>))"

end