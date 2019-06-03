section \<open>Message Justification\<close>

theory MessageJustification

imports Main CBCCasper "Libraries/LaTeXsugar"

begin

(* ###################################################### *)
(* Message justification *)
(* ###################################################### *)

definition (in Params) message_justification :: "message rel"
  where 
    "message_justification = {(m1, m2). {m1, m2} \<subseteq> M \<and> justified m1 m2}" 

lemma (in Protocol) transitivity_of_justifications :
  "trans message_justification"
  apply (simp add: trans_def message_justification_def justified_def)
  by (meson Params.M_type Params.state_is_in_pow_Mi Protocol_axioms contra_subsetD)

lemma (in Protocol) irreflexivity_of_justifications :
  "irrefl message_justification"
  apply (simp add: irrefl_def message_justification_def justified_def)
  apply (simp add: M_def)
  apply auto
proof -
  fix n m
  assume "est m \<in> C" 
  assume "sender m \<in> V"
  assume "justification m \<in> \<Sigma>i (V, C, \<epsilon>) n" 
  assume "est m \<in> \<epsilon> (justification m)" 
  assume "m \<in> justification m"
  have  "m \<in> Mi (V, C, \<epsilon>) (n - 1)"
    by (smt Mi.simps One_nat_def Params.\<Sigma>i_subset_Mi Pow_iff Suc_pred \<open>est m \<in> C\<close> \<open>est m \<in> \<epsilon> (justification m)\<close> \<open>justification m \<in> \<Sigma>i (V, C, \<epsilon>) n\<close> \<open>m \<in> justification m\<close> \<open>sender m \<in> V\<close> add.right_neutral add_Suc_right diff_is_0_eq' diff_le_self diff_zero mem_Collect_eq not_gr0 subsetCE)
  then have  "justification m \<in> \<Sigma>i (V, C, \<epsilon>) (n - 1)"
    using Mi.simps by blast
  then have  "justification m \<in> \<Sigma>i (V, C, \<epsilon>) 0"
    apply (induction n)
    apply simp
    by (smt Mi.simps One_nat_def Params.\<Sigma>i_subset_Mi Pow_iff Suc_pred \<open>m \<in> justification m\<close> add.right_neutral add_Suc_right diff_Suc_1 mem_Collect_eq not_gr0 subsetCE subsetCE)
  then have "justification m \<in> {\<emptyset>}"
    by simp
  then show False
    using \<open>m \<in> justification m\<close> by blast
qed

lemma (in Protocol) message_cannot_justify_itself :
  "(\<forall> m \<in> M. \<not> justified m m)"
proof -
  have "irrefl message_justification"
    using irreflexivity_of_justifications by simp  
  then show ?thesis
    by (simp add: irreflexivity_of_justifications irrefl_def message_justification_def)
qed

lemma (in Protocol) justification_is_strict_partial_order_on_M :
  "strict_partial_order message_justification"
  apply (simp add: strict_partial_order_def)
  by (simp add: irreflexivity_of_justifications transitivity_of_justifications)

lemma (in Protocol) monotonicity_of_justifications :
  "\<forall> m m' \<sigma>. m \<in> M \<and> \<sigma> \<in> \<Sigma> \<and> justified m' m \<longrightarrow> justification m' \<subseteq> justification m"
  apply simp
  by (meson M_type justified_def message_in_state_is_valid state_is_in_pow_Mi)

lemma (in Protocol) strict_monotonicity_of_justifications :
  "\<forall> m m' \<sigma>. m \<in> M \<and> \<sigma> \<in> \<Sigma> \<and> justified m' m \<longrightarrow> justification m' \<subset> justification m"
  by (metis M_type message_cannot_justify_itself  justified_def message_in_state_is_valid monotonicity_of_justifications psubsetI)

lemma (in Protocol) justification_implies_different_messages :
  "\<forall> m m'. m \<in> M \<and> m' \<in> M \<longrightarrow> justified m' m \<longrightarrow> m \<noteq> m'"
  using message_cannot_justify_itself by auto

lemma (in Protocol) only_valid_message_is_justified :
  "\<forall> m \<in> M. \<forall> m'. justified m' m \<longrightarrow> m' \<in> M"
  apply (simp add: justified_def)
  using Params.M_type message_in_state_is_valid by blast

lemma (in Protocol) justified_message_exists_in_Mi_n_minus_1 :
  "\<forall> n m m'. n \<in> \<nat> 
  \<longrightarrow> justified m' m
  \<longrightarrow> m \<in> Mi (V, C, \<epsilon>) n  
  \<longrightarrow>  m' \<in> Mi (V, C, \<epsilon>) (n - 1)"
proof -
  have "\<forall> n m m'. justified m' m
  \<longrightarrow> m \<in> Mi (V, C, \<epsilon>) n  
  \<longrightarrow> m \<in> M \<and> m' \<in> M
  \<longrightarrow> m' \<in> Mi (V, C, \<epsilon>) (n - 1)"
    apply (rule, rule, rule, rule, rule, rule)
  proof -
    fix n m m'
    assume "justified m' m" 
    assume "m \<in> Mi (V, C, \<epsilon>) n"
    assume "m \<in> M \<and> m' \<in> M"
    then have "justification m \<in> \<Sigma>i (V,C,\<epsilon>) n"
      using Mi.simps \<open>m \<in> Mi (V, C, \<epsilon>) n\<close> by blast
    then have "justification m \<in>  Pow (Mi (V,C,\<epsilon>) (n - 1))"
      by (metis (no_types, lifting) Suc_diff_Suc \<Sigma>i.simps(1) \<Sigma>i_subset_Mi \<open>justified m' m\<close> add_leE diff_add diff_le_self empty_iff justified_def neq0_conv plus_1_eq_Suc singletonD subsetCE)
    show "m' \<in> Mi (V, C, \<epsilon>) (n - 1)"
      using \<open>justification m \<in> Pow (Mi (V, C, \<epsilon>) (n - 1))\<close> \<open>justified m' m\<close> justified_def by auto
  qed
  then show ?thesis
    by (metis (no_types, lifting) M_def UN_I only_valid_message_is_justified)
qed  

lemma (in Protocol) monotonicity_of_card_of_justification : 
  "\<forall> m m'. m \<in> M 
  \<longrightarrow> justified m' m 
  \<longrightarrow> card (justification m') < card (justification m)"
  by (meson M_type Protocol.strict_monotonicity_of_justifications Protocol_axioms justification_is_finite psubset_card_mono)

(* TODO: Use `wf` in HOL/Wellfounded.thy #84 *)
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

lemma (in Protocol) message_in_state_is_strict_subset_of_the_state :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> m \<in> \<sigma>. justification m \<subset> \<sigma>"
  using justification_implies_different_messages justified_def message_in_state_is_valid state_is_in_pow_Mi by fastforce

end 