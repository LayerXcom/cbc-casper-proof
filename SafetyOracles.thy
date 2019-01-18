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
fun from_sender :: "(validator * state) \<Rightarrow> message set"
  where
    "from_sender (v, \<sigma>) = {m. m \<in> \<sigma> \<and> sender m = v}"
     
(* Definition 7.3 *)
fun later_from :: "(message * validator * state) \<Rightarrow> message set"
  where
    "later_from (m, v, \<sigma>) = {m'. m' \<in> \<sigma> \<and> sender m' = v \<and> later (m', m)}"
 
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
    "latest_estimates_from_honest_validators (\<sigma>, v) = 
      {est m | m. m \<in> latest_messages_from_honest_validators (\<sigma>, v)}"

(* Definition 7.7 *)
fun latest_justifications_from_honest_validators :: "(state * validator) \<Rightarrow> state set"
  where
    "latest_justifications_from_honest_validators (\<sigma>, v) = 
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
definition weight_measure :: "params \<Rightarrow> validator set \<Rightarrow> real"
  where
    "weight_measure params v_set = sum (W params) v_set"

(* Definition 7.11 *)
fun is_majority :: "params \<Rightarrow> (validator set * state) \<Rightarrow> bool"
  where
    "is_majority params (v_set, \<sigma>) = (weight_measure params v_set > (weight_measure params (V params) - weight_measure params (equivocating_validators \<sigma>)) div 2)"
   
(* Definition 7.12 *)
definition is_majority_driven :: "params \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "is_majority_driven params p = (\<forall> \<sigma> c. \<sigma> \<in> \<Sigma> params \<and> is_majority params (agreeing_validators (p, \<sigma>), \<sigma>) \<longrightarrow> c \<in> \<epsilon> params \<sigma> \<and> p c)"

(* Definition 7.13 *)
definition is_max_driven :: "params \<Rightarrow> consensus_value_property \<Rightarrow> bool"
  where
    "is_max_driven params p =
      (\<forall> \<sigma> c. weight_measure params (agreeing_validators (p, \<sigma>)) > weight_measure params (disagreeing_validators (p, \<sigma>)) \<longrightarrow> c \<in> \<epsilon> params  \<sigma> \<and> p c)"

(* Definition 7.14 *)
fun later_disagreeing_validators :: "(consensus_value_property * message * validator * state) \<Rightarrow> message set"
  where 
    "later_disagreeing_validators (p, m, v, \<sigma>) = {m'. m' \<in> later_from (m, v, \<sigma>) \<and> \<not> p (est m')}"

(* Definition 7.15 *)
(* `the_elem` is built-in  *)


(* Section 7.2: Validator Cliques *)

(* Definition 7.16: Clique with 1 layers *)
fun is_clique :: "(validator set * consensus_value_property * state) \<Rightarrow> bool"
 where
   "is_clique (v_set, p, \<sigma>) = 
     (\<forall> v \<in> v_set. v_set \<subseteq> agreeing_validators (p, the_elem (latest_justifications_from_honest_validators (\<sigma>, v)))
     \<and> (\<forall> v' \<in> v_set. later_disagreeing_validators (p, the_elem (latest_messages_from_honest_validators (the_elem (latest_justifications_from_honest_validators (\<sigma>, v)), v')), v', \<sigma>) = \<emptyset>))"


(* Section 7.3: Cliques Survive Messages from Validators Outside Clique *)

(* Definition 7.17 *)
fun minimal_transitions :: "params \<Rightarrow> (state * state) set"
  where
    "minimal_transitions params = {(\<sigma>, \<sigma>') | \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma>t params \<and> \<sigma>' \<in> \<Sigma>t params \<and> is_future_state (\<sigma>', \<sigma>) \<and> \<sigma> \<noteq> \<sigma>'
      \<and> (\<nexists> \<sigma>''. \<sigma>'' \<in> \<Sigma> params \<and> is_future_state (\<sigma>'', \<sigma>) \<and> is_future_state (\<sigma>', \<sigma>'') \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>'' \<noteq> \<sigma>')}"

(* Temporary lemmas for minimal_transition_implies_recieving_a_single_message *)
lemma no_intermidiate_implies_difference_is_singleton :
  "\<forall> A B. A \<subseteq> B \<and> A \<noteq> B \<longrightarrow> (\<nexists> C. A \<subseteq> C \<and> C \<subseteq> B \<and> A \<noteq> C \<and> B \<noteq> C) \<longrightarrow> is_singleton (B - A)"    
  apply simp
  by (smt DiffD1 DiffD2 Diff_eq_empty_iff Diff_insert_absorb Diff_subset double_diff insert_subset is_singleton_def psubsetI psubset_imp_ex_mem)

lemma difference_is_singleton_implies_no_intermidiate :
  "\<forall> A B. A \<subseteq> B \<and> A \<noteq> B \<longrightarrow> is_singleton (B - A) \<longrightarrow> (\<nexists> C. A \<subseteq> C \<and> C \<subseteq> B \<and> A \<noteq> C \<and> B \<noteq> C)"
  by (smt Diff_cancel Diff_eq_empty_iff Diff_insert0 double_diff insert_Diff is_singleton_def)

lemma "set_difference_and_singleton" :
  "\<forall> A B. A \<subseteq> B \<and> A \<noteq> B \<longrightarrow> (\<nexists> C. A \<subseteq> C \<and> C \<subseteq> B \<and> A \<noteq> C \<and> B \<noteq> C) \<longleftrightarrow> is_singleton (B - A)"
  using no_intermidiate_implies_difference_is_singleton difference_is_singleton_implies_no_intermidiate by metis

lemma no_intermidiate_implies_difference_is_singleton_with_set :
  "\<forall> \<sigma> \<sigma>' M. \<sigma> \<in> Pow M \<and> \<sigma>' \<in> Pow M 
  \<longrightarrow> \<sigma> \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>' 
  \<longrightarrow> (\<nexists> \<sigma>''. \<sigma>'' \<in> Pow M \<and> \<sigma> \<subseteq> \<sigma>'' \<and> \<sigma>'' \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>''\<noteq> \<sigma>')
  \<longrightarrow> is_singleton {m. m \<in> M \<inter> \<sigma>'- \<sigma>}"
  by (metis Collect_mem_eq Int_absorb2  Pow_iff inf_commute no_intermidiate_implies_difference_is_singleton subset_trans)

lemma state_difference_is_valid_message :
  "\<forall> params \<sigma> \<sigma>'. is_valid_params params \<and> \<sigma> \<in> \<Sigma> params \<and> \<sigma>' \<in> \<Sigma> params
  \<longrightarrow> is_future_state(\<sigma>', \<sigma>)
  \<longrightarrow> \<sigma>' - \<sigma> \<subseteq> M params"
  apply (simp add: \<Sigma>_def M_def)
sorry

lemma "A \<subseteq> B \<and> is_singleton {a. a \<in> A \<inter> B} \<longrightarrow> is_singleton A"
  by (metis Collect_mem_eq inf.orderE)

(* A minimal transition corresponds to recieving a single new message with justification drawn from the initial
protocol state *)
lemma minimal_transition_implies_recieving_a_single_message :
  "\<forall> params \<sigma> \<sigma>'. is_valid_params params \<and> \<sigma> \<in> \<Sigma>t params \<and> \<sigma>' \<in> \<Sigma>t params
  \<longrightarrow> (\<sigma>, \<sigma>') \<in> minimal_transitions params \<longrightarrow> is_singleton (\<sigma>'- \<sigma>)"
proof -
  have lemma1 :
    "\<forall> params \<sigma> \<sigma>'. is_valid_params params \<and> \<sigma> \<in> \<Sigma>t params \<and> \<sigma>' \<in> \<Sigma>t params
    \<longrightarrow> (\<sigma>, \<sigma>') \<in> minimal_transitions params \<longrightarrow> is_singleton (M params \<inter> \<sigma>'- \<sigma>)"
  proof -
    have minimal_transition_implies_no_intermidiate :
      "\<forall> params \<sigma> \<sigma>'. is_valid_params params \<and> \<sigma> \<in> \<Sigma>t params \<and> \<sigma>' \<in> \<Sigma>t params
      \<longrightarrow> (\<sigma>, \<sigma>') \<in> minimal_transitions params 
      \<longrightarrow> \<sigma> \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>' \<and> (\<nexists> \<sigma>''. \<sigma>'' \<in> \<Sigma> params \<and> \<sigma> \<subseteq> \<sigma>'' \<and> \<sigma>'' \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>''\<noteq> \<sigma>')"
      by simp
    have no_intermidiate_implies_single_message :
      "\<forall> params \<sigma> \<sigma>'. is_valid_params params \<and> \<sigma> \<in> \<Sigma>t params \<and> \<sigma>' \<in> \<Sigma>t params 
      \<longrightarrow> \<sigma> \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>' 
      \<longrightarrow> (\<nexists> \<sigma>''. \<sigma>'' \<in> \<Sigma> params \<and> \<sigma> \<subseteq> \<sigma>'' \<and> \<sigma>'' \<subseteq> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>'' \<and> \<sigma>''\<noteq> \<sigma>')
      \<longrightarrow> is_singleton (M params \<inter> \<sigma>'- \<sigma>)"
      (* TODO  *)
      sorry
    moreover show ?thesis
      sorry  
  have lemma2 : 
    "\<forall> params \<sigma> \<sigma>'. is_valid_params params \<and> \<sigma> \<in> \<Sigma>t params \<and> \<sigma>' \<in> \<Sigma>t params
    \<longrightarrow> is_singleton {m \<in> M params \<inter> \<sigma>'- \<sigma>} \<longrightarrow> is_singleton (\<sigma>' - \<sigma>)"
    using state_difference_is_valid_message
  oops

(* Lemma 11: Minimal transitions do not change Later_From for any non-sender *)
lemma later_from_not_affected_by_minimal_transitions :
  "\<forall> params \<sigma> \<sigma>' m. is_valid_params params \<and> (\<sigma>, \<sigma>') \<in> minimal_transitions params
  \<longrightarrow> m = the_elem (\<sigma>' - \<sigma>)
  \<longrightarrow> (\<forall> v \<in> V params - {sender m}. later_from (m, v, \<sigma>) = later_from (m, v, \<sigma>'))"
  oops

(* Definition 7.18: One layer clique oracle threshold size *) 
fun gt_threshold :: "params \<Rightarrow> (validator set * state) \<Rightarrow> bool"
  where
    "gt_threshold params (v_set, \<sigma>) = (weight_measure params v_set > (weight_measure params v_set) div 2 + t params - weight_measure params (equivocating_validators \<sigma>))"

end
