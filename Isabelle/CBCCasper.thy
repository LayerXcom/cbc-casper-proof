section \<open>CBC Casper\<close>

theory CBCCasper

imports Main HOL.Real "Libraries/Strict_Order" "Libraries/Restricted_Predicates" "Libraries/LaTeXsugar"

begin

(* ###################################################### *)
(* Parameters and protocol definitions *)
(* ###################################################### *)

(* Section 2: Description of CBC Casper *)
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
  \<Sigma>i :: "(validator set \<times> consensus_value set \<times> (message set \<Rightarrow> consensus_value set)) \<Rightarrow> nat \<Rightarrow> state set" and
  Mi :: "(validator set \<times> consensus_value set \<times> (message set \<Rightarrow> consensus_value set)) \<Rightarrow> nat \<Rightarrow> message set"
  where 
    "\<Sigma>i (V,C,\<epsilon>) 0 = {\<emptyset>}"
  | "\<Sigma>i (V,C,\<epsilon>) n = {\<sigma> \<in> Pow (Mi (V,C,\<epsilon>) (n - 1)). finite \<sigma> \<and> (\<forall> m. m \<in> \<sigma> \<longrightarrow> justification m \<subseteq> \<sigma>)}"
  | "Mi (V,C,\<epsilon>) n = {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> (\<Sigma>i (V,C,\<epsilon>) n) \<and> est m \<in> \<epsilon> (justification m)}" 

locale Params =
  fixes V :: "validator set"
  and W :: "validator \<Rightarrow> real"
  and t :: real
  fixes C :: "consensus_value set"
  and \<epsilon> :: "message set \<Rightarrow> consensus_value set"

begin
  definition "\<Sigma> = (\<Union>i\<in>\<nat>. \<Sigma>i (V,C,\<epsilon>) i)"
  definition "M = (\<Union>i\<in>\<nat>. Mi (V,C,\<epsilon>) i)"
  definition is_valid_estimator :: "(state \<Rightarrow> consensus_value set) \<Rightarrow> bool"
    where
      "is_valid_estimator e = (\<forall>\<sigma> \<in> \<Sigma>. e \<sigma> \<in> Pow C - {\<emptyset>})"

  (* FIXME: Rename these lemmas. *)
  lemma \<Sigma>i_subset_Mi: "\<Sigma>i (V,C,\<epsilon>) (n + 1) \<subseteq> Pow (Mi (V,C,\<epsilon>) n)"
    by force

  lemma \<Sigma>i_subset_to_Mi: "\<Sigma>i (V,C,\<epsilon>) n \<subseteq> \<Sigma>i (V,C,\<epsilon>) (n+1) \<Longrightarrow> Mi (V,C,\<epsilon>) n \<subseteq> Mi (V,C,\<epsilon>) (n+1)"
    by auto

  lemma Mi_subset_to_\<Sigma>i: "Mi (V,C,\<epsilon>) n \<subseteq> Mi (V,C,\<epsilon>) (n+1) \<Longrightarrow> \<Sigma>i (V,C,\<epsilon>) (n+1) \<subseteq> \<Sigma>i (V,C,\<epsilon>) (n+2)"
    by auto

  lemma \<Sigma>i_monotonic: "\<Sigma>i (V,C,\<epsilon>) n \<subseteq> \<Sigma>i (V,C,\<epsilon>) (n+1)"
    apply (induction n)
    apply simp
    apply (metis Mi_subset_to_\<Sigma>i Suc_eq_plus1 \<Sigma>i_subset_to_Mi add.commute add_2_eq_Suc)
    done

  lemma Mi_monotonic: "Mi (V,C,\<epsilon>) n \<subseteq> Mi (V,C,\<epsilon>) (n+1)"
    apply (induction n)
    defer
    using \<Sigma>i_monotonic \<Sigma>i_subset_to_Mi apply blast
    apply auto
    done

  lemma \<Sigma>i_monotonicity: "\<forall> m \<in> \<nat>. \<forall> n \<in> \<nat>. m \<le> n \<longrightarrow> \<Sigma>i (V,C,\<epsilon>) m \<subseteq> \<Sigma>i (V,C,\<epsilon>) n"
    using \<Sigma>i_monotonic
    by (metis Suc_eq_plus1 lift_Suc_mono_le)

  lemma Mi_monotonicity: "\<forall> m \<in> \<nat>. \<forall> n \<in> \<nat>. m \<le> n \<longrightarrow> Mi (V,C,\<epsilon>) m \<subseteq> Mi (V,C,\<epsilon>) n"
    using Mi_monotonic
    by (metis Suc_eq_plus1 lift_Suc_mono_le)

  lemma message_is_in_Mi :
    "\<forall> m \<in> M. \<exists> n \<in> \<nat>. m \<in> Mi (V, C, \<epsilon>) (n - 1)"
    apply (simp add: M_def \<Sigma>i.elims)
    by (metis Nats_1 Nats_add One_nat_def diff_Suc_1 plus_1_eq_Suc)

  lemma state_is_in_pow_Mi :
    "\<forall> \<sigma> \<in> \<Sigma>. (\<exists> n \<in> \<nat>. \<sigma> \<in> Pow (Mi (V, C, \<epsilon>) (n - 1)) \<and> (\<forall> m \<in> \<sigma>. justification m \<subseteq> \<sigma>))" 
    apply (simp add: \<Sigma>_def)
    (* Slow proof found by sledgehammer *)
    (* by (smt Mi.simps One_nat_def PowD \<Sigma>i.elims empty_iff insert_iff mem_Collect_eq subsetCE subsetI) *)
    apply auto
    proof -
      fix y :: nat and \<sigma> :: "message set"
      assume a1: "\<sigma> \<in> \<Sigma>i (V, C, \<epsilon>) y"
      assume a2: "y \<in> \<nat>"
      have "\<sigma> \<subseteq> Mi (V, C, \<epsilon>) y"
        using a1 by (meson Params.\<Sigma>i_monotonic Params.\<Sigma>i_subset_Mi Pow_iff contra_subsetD)
      then have "\<exists>n. n \<in> \<nat> \<and> \<sigma> \<subseteq> Mi (V, C, \<epsilon>) (n - 1)"
        using a2 by (metis (no_types) Nats_1 Nats_add diff_Suc_1 plus_1_eq_Suc)
      then show "\<exists>n\<in>\<nat>. \<sigma> \<subseteq> {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>i (V, C, \<epsilon>) (n - Suc 0) \<and> est m \<in> \<epsilon> (justification m)}"
        by auto
    next 
      show "\<And>y \<sigma> m x. y \<in> \<nat> \<Longrightarrow> \<sigma> \<in> \<Sigma>i (V, C, \<epsilon>) y \<Longrightarrow> m \<in> \<sigma> \<Longrightarrow> x \<in> justification m \<Longrightarrow> x \<in> \<sigma>"
        using Params.\<Sigma>i_monotonic by fastforce
    qed

  lemma message_is_in_Mi_n :
    "\<forall> m \<in> M. \<exists> n \<in> \<nat>. m \<in> Mi (V, C, \<epsilon>) n"
    by (smt Mi_monotonic Suc_diff_Suc add_leE diff_add diff_le_self message_is_in_Mi neq0_conv plus_1_eq_Suc subsetCE zero_less_diff)

  lemma message_in_state_is_valid :
    "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma> \<longrightarrow>  m \<in> M"
    apply (rule, rule, rule)
  proof -
    fix \<sigma> m
    assume "\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>"
    have
      "\<exists> n \<in> \<nat>. m \<in> Mi (V, C, \<epsilon>) n
      \<Longrightarrow> m \<in> M"
      using M_def by blast 
    then show
      "m \<in> M"
      apply (simp add: M_def)
      by (smt Mi.simps Params.\<Sigma>i_monotonic PowD Suc_diff_Suc \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>\<close> add_leE diff_add diff_le_self gr0I mem_Collect_eq plus_1_eq_Suc state_is_in_pow_Mi subsetCE zero_less_diff)
  qed

  lemma state_is_subset_of_M : "\<forall> \<sigma> \<in> \<Sigma>. \<sigma> \<subseteq> M"
    using message_in_state_is_valid by blast
  
  lemma state_is_finite : "\<forall> \<sigma> \<in> \<Sigma>. finite \<sigma>"
    apply (simp add:  \<Sigma>_def)
    using Params.\<Sigma>i_monotonic by fastforce

  lemma justification_is_finite : "\<forall> m \<in> M. finite (justification m)"
    apply (simp add:  M_def)
    using Params.\<Sigma>i_monotonic by fastforce

  lemma \<Sigma>is_subseteq_of_pow_M: "\<Sigma> \<subseteq> Pow M"
    by (simp add: state_is_subset_of_M subsetI)

  lemma M_type: "\<And>m. m \<in> M \<Longrightarrow> est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>"
    unfolding M_def \<Sigma>_def
    by auto

end

(* Locale for proofs *)
locale Protocol = Params +
  assumes V_type: "V \<noteq> \<emptyset> \<and> finite V"
  and W_type: "\<forall> v \<in> V. W v > 0"
  and t_type: "0 \<le> t" "t < sum W V"
  and C_type: "card C > 1" "finite C"
  and \<epsilon>_type: "is_valid_estimator \<epsilon>"

lemma (in Protocol) estimates_are_non_empty: "\<And> \<sigma>. \<sigma> \<in> \<Sigma> \<Longrightarrow> \<epsilon> \<sigma> \<noteq> \<emptyset>"
  using is_valid_estimator_def \<epsilon>_type by auto

lemma (in Protocol) estimates_are_subset_of_C: "\<And> \<sigma>. \<sigma> \<in> \<Sigma> \<Longrightarrow> \<epsilon> \<sigma> \<subseteq> C"
  using is_valid_estimator_def \<epsilon>_type by auto

lemma (in Params) empty_set_exists_in_\<Sigma>_0: "\<emptyset> \<in> \<Sigma>i (V, C, \<epsilon>) 0"
  by simp

lemma (in Params) empty_set_exists_in_\<Sigma>: "\<emptyset> \<in> \<Sigma>"
  apply (simp add:  \<Sigma>_def)
  using Nats_0 \<Sigma>i.simps(1) by blast

lemma (in Params) \<Sigma>i_is_non_empty: "\<Sigma>i (V, C, \<epsilon>) n \<noteq> \<emptyset>"
  apply (induction n)
  using empty_set_exists_in_\<Sigma>_0 by auto

lemma (in Params) \<Sigma>is_non_empty: "\<Sigma> \<noteq> \<emptyset>"
  using empty_set_exists_in_\<Sigma> by blast

lemma (in Protocol) estimates_exists_for_empty_set :
  "\<epsilon> \<emptyset> \<noteq> \<emptyset>"
  by (simp add: empty_set_exists_in_\<Sigma> estimates_are_non_empty)

lemma (in Protocol) non_justifying_message_exists_in_M_0: 
  "\<exists> m. m \<in> Mi (V, C, \<epsilon>) 0 \<and> justification m = \<emptyset>" 
  apply auto
proof -
  have "\<epsilon> \<emptyset> \<subseteq> C"
    using Params.empty_set_exists_in_\<Sigma> \<epsilon>_type is_valid_estimator_def by auto
  then show "\<exists>m. est m \<in> C \<and> sender m \<in> V \<and> justification m = \<emptyset> \<and> est m \<in> \<epsilon> (justification m) \<and> justification m = \<emptyset>"
    by (metis V_type all_not_in_conv est.simps estimates_exists_for_empty_set justification.simps sender.simps set_empty subsetCE)
qed  

lemma (in Protocol) Mi_is_non_empty: "Mi (V, C, \<epsilon>) n \<noteq> \<emptyset>"
  apply (induction n)
  using non_justifying_message_exists_in_M_0 apply auto
  using Mi_monotonic empty_iff empty_subsetI by fastforce

lemma (in Protocol) Mis_non_empty: "M \<noteq> \<emptyset>"
  using non_justifying_message_exists_in_M_0 M_def Nats_0 by blast

lemma (in Protocol) C_is_not_empty : "C \<noteq> \<emptyset>"
  using C_type by auto

lemma (in Params) \<Sigma>i_is_subset_of_\<Sigma> :
  "\<forall> n \<in> \<nat>. \<Sigma>i (V, C, \<epsilon>) n \<subseteq> \<Sigma>"
  by (simp add: \<Sigma>_def SUP_upper)

lemma (in Protocol) message_justifying_state_in_\<Sigma>_n_exists_in_M_n :
  "\<forall> n \<in> \<nat>. (\<forall> \<sigma>. \<sigma> \<in> \<Sigma>i (V, C, \<epsilon>) n \<longrightarrow> (\<exists> m. m \<in> Mi (V, C, \<epsilon>) n \<and> justification m = \<sigma>))"
  apply auto
proof -
  fix n \<sigma>
  assume "n \<in> \<nat>"
  and "\<sigma> \<in> \<Sigma>i (V, C, \<epsilon>) n"
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
    using estimates_are_subset_of_C \<Sigma>i_is_subset_of_\<Sigma> \<open>n \<in> \<nat>\<close> \<open>\<sigma> \<in> \<Sigma>i (V, C, \<epsilon>) n\<close> by blast
  ultimately show "\<exists> m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>i (V, C, \<epsilon>) n \<and> est m \<in> \<epsilon> (justification m) \<and> justification m = \<sigma>"
    using Nats_1 One_nat_def
    using \<open>\<sigma> \<in> \<Sigma>i (V, C, \<epsilon>) n\<close> by blast
qed

lemma (in Protocol) \<Sigma>_type: "\<Sigma> \<subset> Pow M"
proof -
  obtain m where "m \<in> Mi (V, C, \<epsilon>) 0 \<and> justification m = \<emptyset>"
    using non_justifying_message_exists_in_M_0 by auto
  then have "{m} \<in> \<Sigma>i (V, C, \<epsilon>) (Suc 0)"
    using Params.\<Sigma>i_subset_Mi by auto
  then have "\<exists> m'. m' \<in>  Mi (V, C, \<epsilon>) (Suc 0) \<and> justification m' = {m}"
    using message_justifying_state_in_\<Sigma>_n_exists_in_M_n Nats_1 One_nat_def by metis
  then obtain m' where "m' \<in>  Mi (V, C, \<epsilon>) (Suc 0) \<and> justification m' = {m}" by auto
  then have "{m'} \<in> Pow M" 
    using M_def
    by (metis Nats_1 One_nat_def PowD PowI Pow_bottom UN_I insert_subset)
  moreover have "{m'} \<notin> \<Sigma>"
    using Params.state_is_in_pow_Mi Protocol_axioms \<open>m' \<in> Mi (V, C, \<epsilon>) (Suc 0) \<and> justification m' = {m}\<close> by fastforce
  ultimately show ?thesis
    using \<Sigma>is_subseteq_of_pow_M by auto
qed

(* M isn't always a strict subset of C \<times> V \<times> \<Sigma>. *)
lemma (in Protocol) M_type_counterexample: 
  "(\<forall> \<sigma>. \<epsilon> \<sigma> = C) \<Longrightarrow> M = {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>}"
  apply (simp add: M_def)
  apply auto
  using \<Sigma>i_is_subset_of_\<Sigma> apply blast
  by (simp add: \<Sigma>_def) 

(* Definition 4.1: Observed validators *)
definition observed :: "message set \<Rightarrow> validator set"
  where
    "observed \<sigma> = {sender m | m. m \<in> \<sigma>}"

lemma (in Protocol) observed_type :
  "\<forall> \<sigma> \<in> Pow M. observed \<sigma> \<in> Pow V"
  using Params.M_type Protocol_axioms observed_def by fastforce

lemma (in Protocol) observed_type_for_state :
  "\<forall> \<sigma> \<in> \<Sigma>. observed \<sigma> \<subseteq> V"
  using Params.M_type Protocol_axioms observed_def state_is_subset_of_M by fastforce

(* Definition 2.8: Protocol state transitions \<rightarrow> *)
fun is_future_state :: "(state * state) \<Rightarrow> bool"
  where
    "is_future_state (\<sigma>1, \<sigma>2) = (\<sigma>1 \<subseteq> \<sigma>2)"

lemma (in Params) state_difference_is_valid_message :
  "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma> \<and> \<sigma>' \<in> \<Sigma>
  \<longrightarrow> is_future_state(\<sigma>, \<sigma>')
  \<longrightarrow> \<sigma>' - \<sigma> \<subseteq> M"
  using state_is_subset_of_M by blast

(* Definition 2.9 *)
definition justified :: "message \<Rightarrow> message \<Rightarrow> bool"
  where
    "justified m1 m2 = (m1 \<in> justification m2)"

(* ###################################################### *)
(* Equivocation *)
(* ###################################################### *)

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
  using observed_type_for_state equivocating_validators_def by blast

lemma (in Protocol) equivocating_validators_is_finite :
  "\<forall> \<sigma> \<in> \<Sigma>. finite (equivocating_validators \<sigma>)"
  using V_type equivocating_validators_type rev_finite_subset by blast

definition (in Params) equivocating_validators_paper :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators_paper \<sigma> = {v \<in> V. is_equivocating \<sigma> v}"

lemma (in Protocol) equivocating_validators_is_equivalent_to_paper :
  "\<forall> \<sigma> \<in> \<Sigma>. equivocating_validators \<sigma> = equivocating_validators_paper \<sigma>"
  by (smt Collect_cong Params.equivocating_validators_paper_def equivocating_validators_def is_equivocating_def mem_Collect_eq observed_type_for_state observed_def subsetCE)

lemma (in Protocol) equivocation_is_monotonic :
  "\<forall> \<sigma> \<sigma>' v. \<sigma> \<in> \<Sigma> \<and> \<sigma>' \<in> \<Sigma> \<and> is_future_state (\<sigma>, \<sigma>') \<and> v \<in> V
  \<longrightarrow> v \<in> equivocating_validators \<sigma>
  \<longrightarrow> v \<in> equivocating_validators \<sigma>'"
  apply (simp add: equivocating_validators_def is_equivocating_def)
  using observed_def by fastforce

(* ###################################################### *)
(* Weight measure *)
(* ###################################################### *)

(* Definition 7.10 *)
definition (in Params) weight_measure :: "validator set \<Rightarrow> real"
  where
    (* "weight_measure v_set = sum W v_set" *)
    "weight_measure v_set = sum W v_set"

lemma (in Params) weight_measure_subset_minus :
  "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<subseteq> B
    \<Longrightarrow>  weight_measure B - weight_measure A = weight_measure (B - A)"
  apply (simp add: weight_measure_def)
  by (simp add: sum_diff)

lemma (in Params) weight_measure_strict_subset_minus :
  "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<subset> B
    \<Longrightarrow>  weight_measure B - weight_measure A = weight_measure (B - A)"
  apply (simp add:  weight_measure_def)
  by (simp add: sum_diff)

lemma (in Params) weight_measure_disjoint_plus :
  "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<inter> B = \<emptyset>
    \<Longrightarrow>  weight_measure A + weight_measure B = weight_measure (A \<union> B)"
  apply (simp add:  weight_measure_def)
  by (simp add: sum.union_disjoint)

lemma (in Protocol) weight_positive :
  "A \<subseteq> V \<Longrightarrow> weight_measure A \<ge> 0"
  apply (simp add:  weight_measure_def)
  using W_type
  by (smt subsetCE sum_nonneg)

lemma (in Protocol) weight_gte_diff :
  "A \<subseteq> V \<Longrightarrow> weight_measure B \<ge> weight_measure B - weight_measure A"
  using weight_positive by auto

lemma (in Protocol) weight_measure_subset_gte_diff :
  "A \<subseteq> V \<Longrightarrow> A \<subseteq> B \<Longrightarrow> weight_measure B \<ge> weight_measure (B - A)"
  using weight_measure_subset_minus V_type weight_gte_diff
  by (smt finite_Diff2 finite_subset sum.infinite weight_measure_def)

lemma (in Protocol) weight_measure_subset_gte :
  "B \<subseteq> V \<Longrightarrow> A \<subseteq> B \<Longrightarrow> weight_measure B \<ge> weight_measure A"
  using W_type V_type
  apply (simp add:  weight_measure_def)
  by (smt DiffD1 Params.weight_measure_def finite_subset subsetCE sum_nonneg weight_measure_subset_minus)
 
lemma (in Protocol) weight_measure_stritct_subset_gt :
  "B \<subseteq> V \<Longrightarrow> A \<subset> B \<Longrightarrow> weight_measure B > weight_measure A" 
proof -
  fix A B
  assume "B \<subseteq> V" 
  and "A \<subset> B" 
  then have "A \<subset> V"
    by auto
  have "finite A \<and> finite B"
    using V_type finite_subset \<open>B \<subseteq> V\<close> \<open>A \<subset> B\<close> by auto
  have "B - A \<noteq> \<emptyset> \<and> B - A \<subseteq> V"
    using \<open>A \<subset> B\<close> \<open>B \<subseteq> V\<close>
    by blast 
  then have "weight_measure (B - A) > 0"
    using W_type
    apply (simp add: weight_measure_def)
    by (meson Diff_eq_empty_iff V_type rev_finite_subset subset_eq sum_pos)    
  have "weight_measure B = weight_measure (B - A) + weight_measure A"
    using weight_measure_strict_subset_minus \<open>B \<subseteq> V\<close> \<open>A \<subset> B\<close> \<open>finite A \<and> finite B\<close>
    by fastforce    
  then show "weight_measure B > weight_measure A"
    using \<open>weight_measure (B - A) > 0\<close>
    by linarith
qed

(* ###################################################### *)
(* Equivocation fault weight *)
(* ###################################################### *)

(* Definition 2.11 *)
definition (in Params) equivocation_fault_weight :: "state \<Rightarrow> real"
  where
    (* "equivocation_fault_weight \<sigma> = sum W (equivocating_validators \<sigma>)" *)
    "equivocation_fault_weight \<sigma> = weight_measure (equivocating_validators \<sigma>)"

lemma (in Protocol) equivocation_fault_weight_is_monotonic :
  "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma> \<and> \<sigma>' \<in> \<Sigma> \<and> is_future_state (\<sigma>, \<sigma>')
  \<longrightarrow> equivocation_fault_weight \<sigma> \<le> equivocation_fault_weight \<sigma>'"
  using equivocation_is_monotonic weight_measure_subset_gte 
  by (smt equivocating_validators_is_finite equivocating_validators_type equivocation_fault_weight_def subset_iff)

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

end
