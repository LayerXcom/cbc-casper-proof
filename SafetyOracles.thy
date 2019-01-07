theory SafetyOracles

imports Main ConsensusSafety

begin

(* Definition 7.1 *)
definition later :: "message \<Rightarrow> message \<Rightarrow> bool"
  where
    "later m1 m2 = (m2 \<in> justification m1)"

(* Definition 7.2 *)
definition from_sender :: "validator \<Rightarrow> state \<Rightarrow> message set"
  where
    "from_sender v s = {m. sender m = v}"
     
(* Definition 7.3 *)
definition later_from :: "message \<Rightarrow> validator \<Rightarrow> state \<Rightarrow> message set"
  where
    "later_from m v s = {m'. sender m' = v \<and> later m' m}"
 
(* Definition 7.4 *)
definition latest_messages :: "state \<Rightarrow> validator \<Rightarrow> message set"
  where
    "latest_messages s v = {m. sender m = v \<and> later_from m v s = \<emptyset>}"

(* Definition 7.5 *)
definition latest_messages_from_honest_validators :: "state \<Rightarrow> validator \<Rightarrow> message set"
  where
    "latest_messages_from_honest_validators s v = 
      (if v \<in> equivocating_validators s then \<emptyset> else latest_messages s v)"

(* Definition 7.6 *)
definition latest_estimates_from_honest_validators :: "state \<Rightarrow> validator \<Rightarrow> consensus_value set"
  where
    "latest_estimates_from_honest_validators s v = 
      {est m | m. m \<in> latest_messages_from_honest_validators s v}"

(* Definition 7.7 *)
definition latest_justifications_from_honest_validators :: "state \<Rightarrow> validator \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators s v = 
      {justification m | m. m \<in> latest_messages_from_honest_validators s v}"

(* Definition 7.8 *)
definition agreeing :: "consensus_value_property \<Rightarrow> state \<Rightarrow> validator set"
  where
    "agreeing p s = {v. \<forall> c. c \<in> latest_estimates_from_honest_validators s v \<and> p c}"

(* Definition 7.9 *)
definition disagreeing :: "consensus_value_property \<Rightarrow> state \<Rightarrow> validator set"
  where
    "disagreeing p s = {v. \<exists> c. c \<in> latest_estimates_from_honest_validators s v \<and> \<not> p c}"

(* Definition 7.10 *)
definition weight_mesure :: "weight \<Rightarrow> validator set \<Rightarrow> int"
  where
    "weight_mesure w v_set = sum w v_set"

(* Definition 7.11 *)
type_synonym all_validators = "validator set"

definition majority :: "all_validators \<Rightarrow> weight \<Rightarrow> validator set \<Rightarrow> state \<Rightarrow> bool"
  where
    "majority all_v_set w v_set s = (weight_mesure w v_set > (weight_mesure w all_v_set - weight_mesure w (equivocating_validators s)) div 2)"
   
(* Definition 7.12 *)
definition majority_driven :: "all_validators \<Rightarrow> weight \<Rightarrow> estimator \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "majority_driven all_v_set w e p = (\<forall> s c. majority all_v_set w (agreeing p s) s \<longrightarrow> c \<in> e w s \<and> p c)"

(* Definition 7.13 *)
definition max_driven :: "weight \<Rightarrow> estimator \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "max_driven w e p =
      (\<forall> s c. weight_mesure w (agreeing p s) > weight_mesure w (disagreeing p s) \<longrightarrow> c \<in> e w s \<and> p c)"

(* Definition 7.14 *)
definition later_disagreeing :: "consensus_value_property \<Rightarrow> message \<Rightarrow> validator \<Rightarrow> state \<Rightarrow> message set"
  where 
    "later_disagreeing p m v s = {m'. m' \<in> later_from m v s \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* NOTE: Define singleton set here *)

end