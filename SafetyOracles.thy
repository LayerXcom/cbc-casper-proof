theory SafetyOracles

imports Main ConsensusSafety

begin

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* Definition 7.1 *)
fun later :: "(message * message) \<Rightarrow> bool"
  where
    "later (m1, m2) = (m2 \<in> justification m1)"

(* Definition 7.2 *)
fun from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender (v, \<sigma>) = {m. m \<in> \<sigma> \<and> sender m = v}"
     
(* Definition 7.3 *)
fun later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = {m'. m \<in> \<sigma> \<and> sender m' = v \<and> later (m', m)}"
 
(* Definition 7.4 *)
fun latest_messages :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages (\<sigma>, v) = {m. m \<in> \<sigma> \<and> sender m = v \<and> later_from (m, v, \<sigma>) = \<emptyset>}"

(* Definition 7.5 *)
fun latest_messages_from_honest_validators :: "(state *validator) \<Rightarrow> message set"
  where
    "latest_messages_from_honest_validators (\<sigma>, v) = 
      (if v \<in> equivocating_validators \<sigma> then \<emptyset> else latest_messages (\<sigma>, v))"

(* Definition 7.6 *)
fun latest_estimates_from_honest_validators :: "(state * validator) \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_honest_validators(\<sigma>, v) = 
      {est m | m. m \<in> latest_messages_from_honest_validators(\<sigma>, v)}"

(* Definition 7.7 *)
fun latest_justifications_from_honest_validators :: "(state * validator) \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators(\<sigma>, v) = 
      {justification m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

(* Definition 7.8 *)
fun agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators (p, \<sigma>) = {v. \<forall> c. c \<in> latest_estimates_from_honest_validators (\<sigma>, v) \<and> p c}"

(* Definition 7.9 *)
fun disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators (p, \<sigma>) = {v. \<exists> c. c \<in> latest_estimates_from_honest_validators (\<sigma>, v) \<and> \<not> p c}"

(* Definition 7.10 *)
definition weight_measure :: "params \<Rightarrow> validator set \<Rightarrow> int"
  where
    "weight_measure params v_set = sum (W params) v_set"

(* Definition 7.11 *)
fun is_majority :: "params \<Rightarrow> (validator set * state) \<Rightarrow> bool"
  where
    "is_majority params (v_set, \<sigma>) = (weight_measure params v_set > (weight_measure params (V params) - weight_measure params (equivocating_validators \<sigma>)) div 2)"
   
(* Definition 7.12 *)
definition is_majority_driven :: "params \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven params p = (\<forall> \<sigma> c. is_majority params (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> c \<in> \<epsilon> params (W params) \<sigma> \<and> p c)"

(* Definition 7.13 *)
definition is_max_driven :: "params \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven params p =
      (\<forall> \<sigma> c. weight_measure params (agreeing_validators (p, \<sigma>)) > weight_measure params (disagreeing_validators (p, \<sigma>)) \<longrightarrow> c \<in> \<epsilon> params (W params) \<sigma> \<and> p c)"

(* Definition 7.14 *)
fun later_disagreeing_validators :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_validators (p, m, v, \<sigma>) = {m'. m' \<in> later_from (m, v, \<sigma>) \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* NOTE: Define singleton set here *)

(* Section 7.2: Validator Cliques *)

(* Definition: 7.16 *)
(* NOTE: Clique with 1 layers *)
fun is_cliquie :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique (v_set, p, \<sigma>) = (\<forall> v. v \<in> v_set \<and> (v_set \<subseteq> agreeing_validators (p, latest_justifications_from_honest_validators (\<sigma>, v)))
     \<and> (\<forall> v'. v' \<in> v_set \<and> later_disagreeing_validators (p, latest_messages_from_honest_validators (latest_justifications_from_honest_validators (\<sigma>, v), v'), \<sigma>) = \<emptyset>))"


end