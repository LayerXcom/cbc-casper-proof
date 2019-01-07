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
    "latest_messages_from_honest_validators s v = (if v \<in> equivocating_validators s then \<emptyset>
      else latest_messages s v)"
