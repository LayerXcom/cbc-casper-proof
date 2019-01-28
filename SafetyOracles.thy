theory SafetyOracles

imports Main CBCCasper ConsensusSafety

begin

(* Section 7: Safety Oracles *)
(* Section 7.1 Preliminary Definitions *)

(* Definition 7.1 *)
fun later :: "(message * message) \<Rightarrow> bool"
  where
    "later (m1, m2) = (m2 \<in> justification m1)"

(* Definition 7.2 *)
fun (in Protocol) from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender (v, \<sigma>) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v}"
     
(* Definition 7.3 *)
fun (in Protocol) later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = {m' \<in> M. m \<in> \<sigma> \<and> sender m' = v \<and> later (m', m)}"
 
(* Definition 7.4 *)
fun (in Protocol) latest_messages :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages (\<sigma>, v) = {m \<in> M. m \<in> \<sigma> \<and> sender m = v \<and> later_from (m, v, \<sigma>) = \<emptyset>}"

(* Definition 7.5 *)
fun (in Protocol) latest_messages_from_honest_validators :: "(state * validator) \<Rightarrow> message set"
  where
    "latest_messages_from_honest_validators (\<sigma>, v) = 
      (if v \<in> equivocating_validators \<sigma> then \<emptyset> else latest_messages (\<sigma>, v))"

(* Definition 7.6 *)
fun (in Protocol) latest_estimates_from_honest_validators:: "(state * validator) \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_honest_validators (\<sigma>, v) = 
      {est m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

lemma (in Protocol) latest_estimates_from_honest_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_estimates_from_honest_validators (\<sigma>, v) \<subseteq> C"
  using M_type by auto

(* Definition 7.7 *)
fun (in Protocol) latest_justifications_from_honest_validators :: "(state * validator) \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators (\<sigma>, v) = 
      {justification m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

lemma (in Protocol) latest_justifications_from_honest_validators_type :
  "\<forall> \<sigma> v. \<sigma> \<in> \<Sigma> \<and> v \<in> V \<longrightarrow> latest_justifications_from_honest_validators (\<sigma>, v) \<subseteq> \<Sigma>"
  using M_type by auto

(* Definition 7.8 *)
fun (in Protocol) agreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators (p, \<sigma>) = {v \<in> V. \<forall> c \<in> C. c \<in> latest_estimates_from_honest_validators (\<sigma>, v) \<and> p c}"

(* Definition 7.9 *)
fun (in Protocol) disagreeing_validators :: "(consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators (p, \<sigma>) = {v \<in> V. \<exists> c \<in> C. c \<in> latest_estimates_from_honest_validators (\<sigma>, v) \<and> \<not> p c}"

(* Definition 7.10 *)
definition (in Protocol) weight_measure :: "validator set \<Rightarrow> real"
  where
    "weight_measure v_set = sum W v_set"

(* Definition 7.11 *)
fun (in Protocol) is_majority :: "(validator set * state) \<Rightarrow> bool"
  where
    "is_majority (v_set, \<sigma>) = (weight_measure v_set > (weight_measure V - weight_measure (equivocating_validators \<sigma>)) div 2)"
   
(* Definition 7.12 *)
definition (in Protocol) is_majority_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven p = (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> is_majority (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> c \<in> \<epsilon> \<sigma> \<and> p c)"

(* Definition 7.13 *)
definition (in Protocol) is_max_driven :: "consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven p =
      (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> \<and> c \<in> C \<and> weight_measure (agreeing_validators (p, \<sigma>)) > weight_measure (disagreeing_validators (p, \<sigma>)) \<longrightarrow> c \<in> \<epsilon> \<sigma> \<and> p c)"

(* Definition 7.14 *)
fun (in Protocol) later_disagreeing_messages :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_messages (p, m, v, \<sigma>) = {m' \<in> M. m' \<in> later_from (m, v, \<sigma>) \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* NOTE: Define singleton set here *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)

end