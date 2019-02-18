theory CBCCasper

imports Main HOL.Real "Libraries/Strict_Order"

begin

(* ###################################################### *)
(* Section 2: Description of CBC Casper *)
(* ###################################################### *)

(* Section 2.1: CBC Casper "Parameters" *)

notation Set.empty ("\<emptyset>")

(* Definition 2.1 ~ 2.5 *)
typedecl validator

typedecl consensus_value

(* NOTE: list is used here because set can not be used for recursive definition. *)
datatype message =
  Message "consensus_value * validator * message list"

type_synonym state = "message set"

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
    "justification (Message (_, _, s)) = set s"

(* \<Sigma>, M Construction
   NOTE: we cannot refer to the definitions from locale to its context *)
fun
  \<Sigma>_i :: "(validator set \<times> consensus_value set \<times> (message set \<Rightarrow> consensus_value set)) \<Rightarrow> nat \<Rightarrow> state set" and
  M_i :: "(validator set \<times> consensus_value set \<times> (message set \<Rightarrow> consensus_value set)) \<Rightarrow> nat \<Rightarrow> message set"
  where 
    "\<Sigma>_i (V,C,\<epsilon>) 0 = {\<emptyset>}"
  | "\<Sigma>_i (V,C,\<epsilon>) n = {\<sigma> \<in> Pow (M_i (V,C,\<epsilon>) (n - 1)). finite \<sigma> \<and> (\<forall> m. m \<in> \<sigma> \<longrightarrow> justification m \<subseteq> \<sigma>)}"
  | "M_i (V,C,\<epsilon>) n = {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> (\<Sigma>_i (V,C,\<epsilon>) n) \<and> est m \<in> \<epsilon> (justification m)}" 

locale Params =
  fixes V :: "validator set"
  and W :: "validator \<Rightarrow> real"
  and t :: real
  fixes C :: "consensus_value set"
  and \<epsilon> :: "message set \<Rightarrow> consensus_value set"

begin
  definition "\<Sigma> = (\<Union>i\<in>\<nat>. \<Sigma>_i (V,C,\<epsilon>) i)"
  definition "M = (\<Union>i\<in>\<nat>. M_i (V,C,\<epsilon>) i)"
  definition is_valid_estimator :: "(state \<Rightarrow> consensus_value set) \<Rightarrow> bool"
    where
      "is_valid_estimator e = (\<forall>\<sigma> \<in> \<Sigma>. e \<sigma> \<in> Pow C - {\<emptyset>})"

  (* FIXME: Rename these lemmas. *)
  lemma \<Sigma>i_subset_Mi: "\<Sigma>_i (V,C,\<epsilon>) (n + 1) \<subseteq> Pow (M_i (V,C,\<epsilon>) n)"
    by force

  lemma \<Sigma>i_subset_to_Mi: "\<Sigma>_i (V,C,\<epsilon>) n \<subseteq> \<Sigma>_i (V,C,\<epsilon>) (n+1) \<Longrightarrow> M_i (V,C,\<epsilon>) n \<subseteq> M_i (V,C,\<epsilon>) (n+1)"
    by auto

  lemma Mi_subset_to_\<Sigma>i: "M_i (V,C,\<epsilon>) n \<subseteq> M_i (V,C,\<epsilon>) (n+1) \<Longrightarrow> \<Sigma>_i (V,C,\<epsilon>) (n+1) \<subseteq> \<Sigma>_i (V,C,\<epsilon>) (n+2)"
    by auto

  lemma \<Sigma>i_monotonic: "\<Sigma>_i (V,C,\<epsilon>) n \<subseteq> \<Sigma>_i (V,C,\<epsilon>) (n+1)"
    apply (induction n)
    apply simp
    apply (metis Mi_subset_to_\<Sigma>i Suc_eq_plus1 \<Sigma>i_subset_to_Mi add.commute add_2_eq_Suc)
    done

  lemma Mi_monotonic: "M_i (V,C,\<epsilon>) n \<subseteq> M_i (V,C,\<epsilon>) (n+1)"
    apply (induction n)
    defer
    using \<Sigma>i_monotonic \<Sigma>i_subset_to_Mi apply blast
    apply auto
    done

  lemma message_is_in_M_i :
    "\<forall> m \<in> M. \<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)"
    apply (simp add: M_def \<Sigma>_i.elims)
    by (metis Nats_1 Nats_add One_nat_def diff_Suc_1 plus_1_eq_Suc)

  lemma state_is_in_pow_M_i :
    "\<forall> \<sigma> \<in> \<Sigma>. (\<exists> n \<in> \<nat>. \<sigma> \<in> Pow (M_i (V, C, \<epsilon>) (n - 1)) \<and> (\<forall> m \<in> \<sigma>. justification m \<subseteq> \<sigma>))" 
    apply (simp add: \<Sigma>_def)
    (* Slow proof found by sledgehammer *)
    (* by (smt M_i.simps One_nat_def PowD \<Sigma>_i.elims empty_iff insert_iff mem_Collect_eq subsetCE subsetI) *)
    apply auto
    proof -
      fix y :: nat and \<sigma> :: "message set"
      assume a1: "\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) y"
      assume a2: "y \<in> \<nat>"
      have "\<sigma> \<subseteq> M_i (V, C, \<epsilon>) y"
        using a1 by (meson Params.\<Sigma>i_monotonic Params.\<Sigma>i_subset_Mi Pow_iff contra_subsetD)
      then have "\<exists>n. n \<in> \<nat> \<and> \<sigma> \<subseteq> M_i (V, C, \<epsilon>) (n - 1)"
        using a2 by (metis (no_types) Nats_1 Nats_add diff_Suc_1 plus_1_eq_Suc)
      then show "\<exists>n\<in>\<nat>. \<sigma> \<subseteq> {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>_i (V, C, \<epsilon>) (n - Suc 0) \<and> est m \<in> \<epsilon> (justification m)}"
        by auto
    next 
      show "\<And>y \<sigma> m x. y \<in> \<nat> \<Longrightarrow> \<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) y \<Longrightarrow> m \<in> \<sigma> \<Longrightarrow> x \<in> justification m \<Longrightarrow> x \<in> \<sigma>"
        using Params.\<Sigma>i_monotonic by fastforce
    qed

  lemma message_is_in_M_i_n :
    "\<forall> m \<in> M. \<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) n"
    by (smt Mi_monotonic Suc_diff_Suc add_leE diff_add diff_le_self message_is_in_M_i neq0_conv plus_1_eq_Suc subsetCE zero_less_diff)

  lemma message_in_state_is_valid :
    "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma> \<longrightarrow>  m \<in> M"
    apply (rule, rule, rule)
  proof -
    fix \<sigma> m
    assume "\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>"
    have
      "\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) n
      \<Longrightarrow> m \<in> M"
      using M_def by blast 
    then show
      "m \<in> M"
      apply (simp add: M_def)
      by (smt M_i.simps Params.\<Sigma>i_monotonic PowD Suc_diff_Suc \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>\<close> add_leE diff_add diff_le_self gr0I mem_Collect_eq plus_1_eq_Suc state_is_in_pow_M_i subsetCE zero_less_diff)
  qed

  lemma state_is_subset_of_M : "\<forall> \<sigma> \<in> \<Sigma>. \<sigma> \<subseteq> M"
    using message_in_state_is_valid by blast
  
  lemma state_difference_is_valid_message :
    "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma> \<and> \<sigma>' \<in> \<Sigma>
    \<longrightarrow> is_future_state(\<sigma>, \<sigma>')
    \<longrightarrow> \<sigma>' - \<sigma> \<subseteq> M"
    using state_is_subset_of_M by blast

  lemma state_is_finite : "\<forall> \<sigma> \<in> \<Sigma>. finite \<sigma>"
    apply (simp add:  \<Sigma>_def)
    using Params.\<Sigma>i_monotonic by fastforce

  lemma justification_is_finite : "\<forall> m \<in> M. finite (justification m)"
    apply (simp add:  M_def)
    using Params.\<Sigma>i_monotonic by fastforce

  lemma \<Sigma>_is_subseteq_of_pow_M: "\<Sigma> \<subseteq> Pow M"
    by (simp add: state_is_subset_of_M subsetI)

  lemma M_type: "\<And>m. m \<in> M \<Longrightarrow> est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>"
    unfolding M_def \<Sigma>_def
    by auto

end

(* Locale for proofs *)
locale Protocol = Params +
  assumes V_type: "V \<noteq> \<emptyset>"
  and W_type: "\<And>w. w \<in> range W \<Longrightarrow> w > 0"
  and t_type: "0 \<le> t" "t < Sum (W ` V)"
  and C_type: "card C > 1"
  and \<epsilon>_type: "is_valid_estimator \<epsilon>"

lemma (in Protocol) estimates_are_non_empty: "\<And> \<sigma>. \<sigma> \<in> \<Sigma> \<Longrightarrow> \<epsilon> \<sigma> \<noteq> \<emptyset>"
  using is_valid_estimator_def \<epsilon>_type by auto

lemma (in Protocol) estimates_are_subset_of_C: "\<And> \<sigma>. \<sigma> \<in> \<Sigma> \<Longrightarrow> \<epsilon> \<sigma> \<subseteq> C"
  using is_valid_estimator_def \<epsilon>_type by auto

lemma (in Params) empty_set_exists_in_\<Sigma>_0: "\<emptyset> \<in> \<Sigma>_i (V, C, \<epsilon>) 0"
  by simp

lemma (in Params) empty_set_exists_in_\<Sigma>: "\<emptyset> \<in> \<Sigma>"
  apply (simp add:  \<Sigma>_def)
  using Nats_0 \<Sigma>_i.simps(1) by blast

lemma (in Params) \<Sigma>_i_is_non_empty: "\<Sigma>_i (V, C, \<epsilon>) n \<noteq> \<emptyset>"
  apply (induction n)
  using empty_set_exists_in_\<Sigma>_0 by auto

lemma (in Params) \<Sigma>_is_non_empty: "\<Sigma> \<noteq> \<emptyset>"
  using empty_set_exists_in_\<Sigma> by blast

lemma (in Protocol) estimates_exists_for_empty_set :
  "\<epsilon> \<emptyset> \<noteq> \<emptyset>"
  by (simp add: empty_set_exists_in_\<Sigma> estimates_are_non_empty)

lemma (in Protocol) non_justifying_message_exists_in_M_0: 
  "\<exists> m. m \<in> M_i (V, C, \<epsilon>) 0 \<and> justification m = \<emptyset>" 
  apply auto
proof -
  have "\<epsilon> \<emptyset> \<subseteq> C"
    using Params.empty_set_exists_in_\<Sigma> \<epsilon>_type is_valid_estimator_def by auto
  then show "\<exists>m. est m \<in> C \<and> sender m \<in> V \<and> justification m = \<emptyset> \<and> est m \<in> \<epsilon> (justification m) \<and> justification m = \<emptyset>"
    by (metis V_type all_not_in_conv est.simps estimates_exists_for_empty_set justification.simps sender.simps set_empty subsetCE)
qed  

lemma (in Protocol) M_i_is_non_empty: "M_i (V, C, \<epsilon>) n \<noteq> \<emptyset>"
  apply (induction n)
  using non_justifying_message_exists_in_M_0 apply auto
  using Mi_monotonic empty_iff empty_subsetI by fastforce

lemma (in Protocol) M_is_non_empty: "M \<noteq> \<emptyset>"
  using non_justifying_message_exists_in_M_0 M_def Nats_0 by blast

lemma (in Protocol) C_is_not_empty : "C \<noteq> \<emptyset>"
  using C_type by auto

lemma (in Params) \<Sigma>i_is_subset_of_\<Sigma> :
  "\<forall> n \<in> \<nat>. \<Sigma>_i (V, C, \<epsilon>) n \<subseteq> \<Sigma>"
  by (simp add: \<Sigma>_def SUP_upper)

lemma (in Protocol) message_justifying_state_in_\<Sigma>_n_exists_in_M_n :
  "\<forall> n \<in> \<nat>. (\<forall> \<sigma>. \<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n \<longrightarrow> (\<exists> m. m \<in> M_i (V, C, \<epsilon>) n \<and> justification m = \<sigma>))"
  apply auto
proof -
  fix n \<sigma>
  assume "n \<in> \<nat>"
  and "\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n"
  then have "\<sigma> \<in> \<Sigma>"
    using \<Sigma>i_is_subset_of_\<Sigma> by auto
  have "\<epsilon> \<sigma> \<noteq> \<emptyset>"
    using estimates_are_non_empty \<open>\<sigma> \<in> \<Sigma>\<close> by auto  
  have "finite \<sigma>" 
    using state_is_finite \<open>\<sigma> \<in> \<Sigma>\<close> by auto
  moreover have "\<exists> m. sender m \<in> V \<and> est m \<in> \<epsilon> \<sigma> \<and> justification m = \<sigma>"
    using est.simps sender.simps justification.simps V_type \<open>\<epsilon> \<sigma> \<noteq> \<emptyset>\<close> \<open>finite \<sigma>\<close>
    by (metis all_not_in_conv finite_list)
  moreover have "\<epsilon> \<sigma> \<subseteq> C"
    using estimates_are_subset_of_C \<Sigma>i_is_subset_of_\<Sigma> \<open>n \<in> \<nat>\<close> \<open>\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n\<close> by blast
  ultimately show "\<exists> m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>_i (V, C, \<epsilon>) n \<and> est m \<in> \<epsilon> (justification m) \<and> justification m = \<sigma>"
    using Nats_1 One_nat_def
    using \<open>\<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n\<close> by blast
qed

lemma (in Protocol) \<Sigma>_type: "\<Sigma> \<subset> Pow M"
proof -
  obtain m where "m \<in> M_i (V, C, \<epsilon>) 0 \<and> justification m = \<emptyset>"
    using non_justifying_message_exists_in_M_0 by auto
  then have "{m} \<in> \<Sigma>_i (V, C, \<epsilon>) (Suc 0)"
    using Params.\<Sigma>i_subset_Mi by auto
  then have "\<exists> m'. m' \<in>  M_i (V, C, \<epsilon>) (Suc 0) \<and> justification m' = {m}"
    using message_justifying_state_in_\<Sigma>_n_exists_in_M_n Nats_1 One_nat_def by metis
  then obtain m' where "m' \<in>  M_i (V, C, \<epsilon>) (Suc 0) \<and> justification m' = {m}" by auto
  then have "{m'} \<in> Pow M" 
    using M_def
    by (metis Nats_1 One_nat_def PowD PowI Pow_bottom UN_I insert_subset)
  moreover have "{m'} \<notin> \<Sigma>"
    using Params.state_is_in_pow_M_i Protocol_axioms \<open>m' \<in> M_i (V, C, \<epsilon>) (Suc 0) \<and> justification m' = {m}\<close> by fastforce
  ultimately show ?thesis
    using \<Sigma>_is_subseteq_of_pow_M by auto
qed

(* M isn't always a strict subset of C \<times> V \<times> \<Sigma>. *)
lemma (in Protocol) M_type_counterexample: 
  "(\<forall> \<sigma>. \<epsilon> \<sigma> = C) \<Longrightarrow> M = {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>}"
  apply (simp add: M_def)
  apply auto
  using \<Sigma>i_is_subset_of_\<Sigma> apply blast
  by (simp add: \<Sigma>_def) 

(* Definition 4.1: Observed validators *)
definition observed :: "state \<Rightarrow> validator set"
  where
    "observed \<sigma> = {sender m | m. m \<in> \<sigma>}"

lemma (in Protocol) observed_type :
  "\<forall> \<sigma> \<in> \<Sigma>. observed \<sigma> \<subseteq> V"
  using Params.M_type Protocol_axioms observed_def state_is_subset_of_M by fastforce

(* Definition 2.8: Protocol state transitions \<rightarrow> *)
fun is_future_state :: "(state * state) \<Rightarrow> bool"
  where
    "is_future_state (\<sigma>1, \<sigma>2) = (\<sigma>1 \<subseteq> \<sigma>2)"

(* Definition 2.9 *)
definition justified :: "message \<Rightarrow> message \<Rightarrow> bool"
  where
    "justified m1 m2 = (m1 \<in> justification m2)"

definition equivocation :: "(message * message) \<Rightarrow> bool"
  where
    "equivocation =
      (\<lambda>(m1, m2). sender m1 = sender m2 \<and> m1 \<noteq> m2 \<and> \<not> (justified m1 m2) \<and> \<not> (justified m2 m1))"

(* Definition 2.10 *)
definition is_equivocating :: "state \<Rightarrow> validator \<Rightarrow> bool"
  where
    "is_equivocating \<sigma> v =  (\<exists> m1 \<in> \<sigma>. \<exists> m2 \<in> \<sigma>. equivocation (m1, m2) \<and> sender m1 = v)"

definition equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators \<sigma> = {v \<in> observed \<sigma>. is_equivocating \<sigma> v}"

lemma (in Protocol) equivocating_validators_type :
  "\<forall> \<sigma> \<in> \<Sigma>. equivocating_validators \<sigma> \<subseteq> V"
  using observed_type equivocating_validators_def by blast

definition (in Params) equivocating_validators_paper :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators_paper \<sigma> = {v \<in> V. is_equivocating \<sigma> v}"

lemma (in Protocol) equivocating_validators_is_equivalent_to_paper :
  "\<forall> \<sigma> \<in> \<Sigma>. equivocating_validators \<sigma> = equivocating_validators_paper \<sigma>"
  by (smt Collect_cong Params.equivocating_validators_paper_def equivocating_validators_def is_equivocating_def mem_Collect_eq observed_type observed_def subsetCE)


(* Definition 2.11 *)
definition (in Params) equivocation_fault_weight :: "state \<Rightarrow> real"
  where
    "equivocation_fault_weight \<sigma> = sum W (equivocating_validators \<sigma>)"

(* Definition 2.12 *)
definition (in Params) is_faults_lt_threshold :: "state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold \<sigma> = (equivocation_fault_weight \<sigma> < t)"

definition (in Protocol) \<Sigma>t :: "state set"
  where
    "\<Sigma>t = {\<sigma> \<in> \<Sigma>. is_faults_lt_threshold \<sigma>}" 

lemma (in Protocol) \<Sigma>t_is_subset_of_\<Sigma> : "\<Sigma>t \<subseteq> \<Sigma>"
  using \<Sigma>t_def by auto

(* Definition 3.2 *)
type_synonym state_property = "state \<Rightarrow> bool"

(* Definition 3.7 *)
type_synonym consensus_value_property = "consensus_value \<Rightarrow> bool"


(* ###################################################### *)
(* Message justification and lemmas *)
(* ###################################################### *)

lemma (in Protocol) transitivity_of_justifications :
  "transp_on justified M"
  apply (simp add: transp_on_def)
  by (meson Params.M_type Params.state_is_in_pow_M_i Protocol_axioms contra_subsetD justified_def)

lemma (in Protocol) irreflexivity_of_justifications :
  "irreflp_on justified M"
  apply (simp add: irreflp_on_def)
  apply (simp add: justified_def)
  apply (simp add: M_def)
  apply auto
proof -
  fix n m
  assume "est m \<in> C" 
  assume "sender m \<in> V"
  assume "justification m \<in> \<Sigma>_i (V, C, \<epsilon>) n" 
  assume "est m \<in> \<epsilon> (justification m)" 
  assume "m \<in> justification m"
  have  "m \<in> M_i (V, C, \<epsilon>) (n - 1)"
    by (smt M_i.simps One_nat_def Params.\<Sigma>i_subset_Mi Pow_iff Suc_pred \<open>est m \<in> C\<close> \<open>est m \<in> \<epsilon> (justification m)\<close> \<open>justification m \<in> \<Sigma>_i (V, C, \<epsilon>) n\<close> \<open>m \<in> justification m\<close> \<open>sender m \<in> V\<close> add.right_neutral add_Suc_right diff_is_0_eq' diff_le_self diff_zero mem_Collect_eq not_gr0 subsetCE)
  then have  "justification m \<in> \<Sigma>_i (V, C, \<epsilon>) (n - 1)"
    using M_i.simps by blast
  then have  "justification m \<in> \<Sigma>_i (V, C, \<epsilon>) 0"
    apply (induction n)
    apply simp
    by (smt M_i.simps One_nat_def Params.\<Sigma>i_subset_Mi Pow_iff Suc_pred \<open>m \<in> justification m\<close> add.right_neutral add_Suc_right diff_Suc_1 mem_Collect_eq not_gr0 subsetCE subsetCE)
  then have "justification m \<in> {\<emptyset>}"
    by simp
  then show False
    using \<open>m \<in> justification m\<close> by blast
qed

lemma (in Protocol) justification_is_strict_partial_order_on_M :
  "po_on justified M"
  apply (simp add: po_on_def)
  by (simp add: irreflexivity_of_justifications transitivity_of_justifications)

lemma (in Protocol) monotonicity_of_justifications :
  "\<forall> m m' \<sigma>. m \<in> M \<and> \<sigma> \<in> \<Sigma> \<and> justified m' m \<longrightarrow> justification m' \<subseteq> justification m"
  apply simp
  by (meson M_type justified_def message_in_state_is_valid state_is_in_pow_M_i)

lemma (in Protocol) strict_monotonicity_of_justifications :
  "\<forall> m m' \<sigma>. m \<in> M \<and> \<sigma> \<in> \<Sigma> \<and> justified m' m \<longrightarrow> justification m' \<subset> justification m"
  by (metis M_type irreflexivity_of_justifications irreflp_on_def justified_def message_in_state_is_valid monotonicity_of_justifications psubsetI)

lemma (in Protocol) justification_implies_different_messages :
  "\<forall> m m'. m \<in> M \<and> m' \<in> M \<longrightarrow> justified m' m \<longrightarrow> m \<noteq> m'"
  by (meson irreflexivity_of_justifications irreflp_on_def)

lemma (in Protocol) only_valid_message_is_justified :
  "\<forall> m \<in> M. \<forall> m'. justified m' m \<longrightarrow> m' \<in> M"
  apply (simp add: justified_def)
  using Params.M_type message_in_state_is_valid by blast

lemma (in Protocol) justified_message_exists_in_M_i_n_minus_1 :
  "\<forall> n m m'. n \<in> \<nat> 
  \<longrightarrow> justified m' m
  \<longrightarrow> m \<in> M_i (V, C, \<epsilon>) n  
  \<longrightarrow>  m' \<in> M_i (V, C, \<epsilon>) (n - 1)"
proof -
  have "\<forall> n m m'. justified m' m
  \<longrightarrow> m \<in> M_i (V, C, \<epsilon>) n  
  \<longrightarrow> m \<in> M \<and> m' \<in> M
  \<longrightarrow> m' \<in> M_i (V, C, \<epsilon>) (n - 1)"
    apply (rule, rule, rule, rule, rule, rule)
  proof -
    fix n m m'
    assume "justified m' m" 
    assume "m \<in> M_i (V, C, \<epsilon>) n"
    assume "m \<in> M \<and> m' \<in> M"
    then have "justification m \<in> \<Sigma>_i (V,C,\<epsilon>) n"
      using M_i.simps \<open>m \<in> M_i (V, C, \<epsilon>) n\<close> by blast
    then have "justification m \<in>  Pow (M_i (V,C,\<epsilon>) (n - 1))"
      by (metis (no_types, lifting) Suc_diff_Suc \<Sigma>_i.simps(1) \<Sigma>i_subset_Mi \<open>justified m' m\<close> add_leE diff_add diff_le_self empty_iff justified_def neq0_conv plus_1_eq_Suc singletonD subsetCE)
    show "m' \<in> M_i (V, C, \<epsilon>) (n - 1)"
      using \<open>justification m \<in> Pow (M_i (V, C, \<epsilon>) (n - 1))\<close> \<open>justified m' m\<close> justified_def by auto
  qed
  then show ?thesis
    by (metis (no_types, lifting) M_def UN_I only_valid_message_is_justified)
qed  

lemma (in Protocol) monotonicity_of_card_of_justification : 
  "\<forall> m m'. m \<in> M 
  \<longrightarrow> justified m' m 
  \<longrightarrow> card (justification m') < card (justification m)"
  by (meson M_type Protocol.strict_monotonicity_of_justifications Protocol_axioms justification_is_finite psubset_card_mono)

lemma (in Protocol) justification_is_well_founded_on_M :
  "wfp_on justified M"
proof (rule ccontr) 
  assume "\<not> wfp_on justified M"
  then have "\<exists>f. \<forall>i. f i \<in> M \<and> justified (f (Suc i)) (f i)"
    by (simp add: wfp_on_def)
  then obtain f where "\<forall>i. f i \<in> M \<and> justified (f (Suc i)) (f i)" by auto
  have "\<forall> i. card (justification (f i)) \<le> card (justification (f 0)) - i"
    apply (rule)
  proof -
    fix i
    have "card (justification (f (Suc i))) < card (justification (f i))"
    using \<open>\<forall>i. f i \<in> M \<and> justified (f (Suc i)) (f i)\<close> by (simp add: monotonicity_of_card_of_justification)
    show "card (justification (f i)) \<le> card (justification (f 0)) - i"
      apply (induction i)
      apply simp
      using \<open>card (justification (f (Suc i))) < card (justification (f i))\<close>
      by (smt Suc_diff_le \<open>\<forall>i. f i \<in> M \<and> justified (f (Suc i)) (f i)\<close> diff_Suc_Suc diff_is_0_eq le_iff_add less_Suc_eq_le less_imp_le monotonicity_of_card_of_justification not_less_eq_eq trans_less_add1)  
  qed
  then have "\<exists> i. i = card (justification (f 0)) + Suc 0 \<and> card (justification (f i)) \<le> card (justification (f 0)) - i"
    by blast
  then show False
    using le_0_eq le_simps(2) linorder_not_le monotonicity_of_card_of_justification nat_diff_split order_less_imp_le
    by (metis \<open>\<forall>i. f i \<in> M \<and> justified (f (Suc i)) (f i)\<close> add.right_neutral add_Suc_right)
qed

lemma (in Protocol) subset_of_M_have_minimal_of_justification :
  "\<forall> S \<subseteq> M. S \<noteq> \<emptyset> \<longrightarrow> (\<exists> m_min \<in> S. \<forall> m. justified m m_min \<longrightarrow> m \<notin> S)"
  by (metis justification_is_well_founded_on_M wfp_on_imp_has_min_elt wfp_on_mono)

definition (in Params) state_transition :: "state rel"
  where 
    "state_transition = {(\<sigma>1, \<sigma>2). {\<sigma>1, \<sigma>2} \<subseteq> \<Sigma> \<and> is_future_state(\<sigma>1, \<sigma>2)}" 

lemma (in Params) reflexivity_of_state_transition :
  "refl_on \<Sigma> state_transition"  
  apply (simp add: state_transition_def refl_on_def)
  by auto

lemma (in Params) transitivity_of_state_transition :
  "trans state_transition"  
  apply (simp add: state_transition_def trans_def)
  by auto

lemma (in Params) state_transition_is_preorder :
  "preorder_on \<Sigma> state_transition"
  by (simp add: preorder_on_def reflexivity_of_state_transition transitivity_of_state_transition)

lemma (in Params) antisymmetry_of_state_transition :
  "antisym state_transition"  
  apply (simp add: state_transition_def antisym_def)
  by auto

lemma (in Params) state_transition_is_partial_order :
  "partial_order_on \<Sigma> state_transition"
  by (simp add: partial_order_on_def state_transition_is_preorder antisymmetry_of_state_transition)

end
