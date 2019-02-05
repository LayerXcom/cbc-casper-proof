theory SafetyOracle

imports Main CBCCasper ConsensusSafety LatestMessage

begin

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* Definition 7.1 *)
fun later :: "(message * message) \<Rightarrow> bool"
  where
    "later (m1, m2) = (m2 \<in> justification m1)"
 
(* Definition 7.2 *)
fun (in Params) from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender (v, \<sigma>) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v}"

(* Definition 7.3 *)
fun (in Params) later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = {m' \<in> M. m \<in> \<sigma> \<and> sender m' = v \<and> later (m', m)}"

(* Definition 7.4 *)
fun (in Params) latest_messages :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages (\<sigma>, v) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v \<and> later_from (m, v, \<sigma>) = \<emptyset>}"

(* Definition 7.5 *)
fun (in Params) latest_messages_from_honest_validators :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages_from_honest_validators (\<sigma>, v) = 
      (if v \<in> equivocating_validators \<sigma> then \<emptyset> else latest_messages (\<sigma>, v))"

(* Definition 7.6 *)
fun (in Params) latest_estimates_from_honest_validators:: "(state * validator) \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_honest_validators (\<sigma>, v) = 
      {est m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

lemma (in Protocol) latest_estimates_from_honest_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates_from_honest_validators (\<sigma>, v) \<subseteq> C"
  using M_type by auto

(* Definition 7.7 *)
fun (in Params) latest_justifications_from_honest_validators :: "(state * validator) \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators (\<sigma>, v) = 
      {justification m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

lemma (in Protocol) latest_justifications_from_honest_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_justifications_from_honest_validators (\<sigma>, v) \<subseteq> \<Sigma>"
  using M_type by auto

(* Definition 7.8 *)
fun (in Params) agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators (p, \<sigma>) = {v \<in> V. \<forall> c \<in> latest_estimates_from_honest_validators (\<sigma>, v). p c}"

(* Definition 7.9 *)
fun (in Params) disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators (p, \<sigma>) = {v \<in> V. \<exists> c \<in> latest_estimates_from_honest_validators (\<sigma>, v). \<not> p c}"

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
fun (in Params) later_disagreeing_messages :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_messages (p, m, v, \<sigma>) = {m' \<in> M. m' \<in> later_from (m, v, \<sigma>) \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* `the_elem` is built-in  *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)
fun (in Params) is_clique :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique (v_set, p, \<sigma>) = 
     (\<forall> v \<in> v_set. v_set \<subseteq> agreeing_validators (p, the_elem (latest_justifications_from_honest_validators (\<sigma>, v)))
     \<and>  (\<forall>  v' \<in> v_set. later_disagreeing_messages (p, the_elem (latest_messages_from_honest_validators (the_elem (latest_justifications_from_honest_validators (\<sigma>, v)), v')), v', \<sigma>) = \<emptyset>))"


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