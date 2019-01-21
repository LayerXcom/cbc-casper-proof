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
fun from_sender :: "params \<Rightarrow> (validator * state) \<Rightarrow> message set"
  where
    "from_sender params (v, \<sigma>) = {m \<in> M params. m \<in> \<sigma> \<and> sender m = v}"
     
(* Definition 7.3 *)
fun later_from :: "params \<Rightarrow> (message * validator * state) \<Rightarrow> message set"
  where
    "later_from params (m, v, \<sigma>) = {m' \<in> M params. m \<in> \<sigma> \<and> sender m' = v \<and> later (m', m)}"
 
(* Definition 7.4 *)
fun latest_messages :: "params \<Rightarrow> (state * validator) \<Rightarrow> message set"
  where
    "latest_messages params (\<sigma>, v) = {m \<in> M params. m \<in> \<sigma> \<and> sender m = v \<and> later_from params (m, v, \<sigma>) = \<emptyset>}"

(* Definition 7.5 *)
fun latest_messages_from_honest_validators :: "params \<Rightarrow> (state *validator) \<Rightarrow> message set"
  where
    "latest_messages_from_honest_validators params (\<sigma>, v) = 
      (if v \<in> equivocating_validators params \<sigma> then \<emptyset> else latest_messages params (\<sigma>, v))"

(* Definition 7.6 *)
fun latest_estimates_from_honest_validators :: "params \<Rightarrow> (state * validator) \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_honest_validators params (\<sigma>, v) = 
      {est m | m. m \<in> latest_messages_from_honest_validators params (\<sigma>, v)}"

(* Definition 7.7 *)
fun latest_justifications_from_honest_validators :: "params \<Rightarrow> (state * validator) \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators params (\<sigma>, v) = 
      {justification m | m. m \<in> latest_messages_from_honest_validators params (\<sigma>, v)}"

(* Definition 7.8 *)
fun agreeing_validators :: "params \<Rightarrow> (consensus_value_property * state) \<Rightarrow> validator set"
  where
    "agreeing_validators params (p, \<sigma>) = {v \<in> V params. \<forall> c \<in> C params. c \<in> latest_estimates_from_honest_validators params (\<sigma>, v) \<and> p c}"

(* Definition 7.9 *)
fun disagreeing_validators :: "params \<Rightarrow> (consensus_value_property * state) \<Rightarrow> validator set"
  where
    "disagreeing_validators params (p, \<sigma>) = {v \<in> V params. \<exists> c \<in> C params. c \<in> latest_estimates_from_honest_validators params (\<sigma>, v) \<and> \<not> p c}"

(* Definition 7.10 *)
definition weight_measure :: "params \<Rightarrow> validator set \<Rightarrow> real"
  where
    "weight_measure params v_set = sum (W params) v_set"

(* Definition 7.11 *)
fun is_majority :: "params \<Rightarrow> (validator set * state) \<Rightarrow> bool"
  where
    "is_majority params (v_set, \<sigma>) = 
      (weight_measure params v_set > (weight_measure params (V params) - weight_measure params (equivocating_validators params \<sigma>)) div 2)"
   
(* Definition 7.12 *)
definition is_majority_driven :: "params \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven params p = (\<forall> \<sigma> \<in> \<Sigma> params. is_majority params (agreeing_validators params (p, \<sigma>), \<sigma>) \<longrightarrow> (\<forall> c \<in> \<epsilon> params \<sigma>. p c))"

(* Definition 7.13 *)
definition is_max_driven :: "params \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven params p =
      (\<forall> \<sigma> \<in> \<Sigma> params. weight_measure params (agreeing_validators params (p, \<sigma>)) > weight_measure params (disagreeing_validators params (p, \<sigma>))
        \<longrightarrow> (\<forall> c \<in> \<epsilon> params \<sigma>. p c))"

(* Definition 7.14 *)
fun later_disagreeing_validators :: "params \<Rightarrow> (consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_validators params (p, m, v, \<sigma>) = {m' \<in> M params. m' \<in> later_from params (m, v, \<sigma>) \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* NOTE: Define singleton set here *)

(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)

end