(*  Title:      Strict_Order
    Author:     Ryuya Nakamura <nrryuya@gmail.com>
    Maintainer: Ryuya Nakamura
    License:    LGPL
*)

theory Strict_Order

imports Main

begin

notation Set.empty ("\<emptyset>")

definition "strict_partial_order r \<equiv> trans r \<and> irrefl r"

definition "strict_well_order_on A r \<equiv> strict_linear_order_on A r \<and> wf r"

(* NOTE: In these definitions r is assumed to be strict partial order. *)
definition upper_bound_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "upper_bound_on A r x = (\<forall> y. y \<in> A \<longrightarrow> (y, x) \<in> r \<or> x = y)"

definition maximum_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "maximum_on A r x = (x \<in> A \<and> upper_bound_on A r x)" 

definition minimal_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "minimal_on A r x = (x \<in> A \<and> (\<forall> y. (y, x) \<in> r \<longrightarrow> y \<notin> A))" 

definition maximal_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "maximal_on A r x = (x \<in> A \<and> (\<forall> y. (x, y) \<in> r \<longrightarrow> y \<notin> A))"

lemma maximal_and_maximum_coincide_for_strict_linear_order :
  "strict_linear_order_on A r \<Longrightarrow> maximal_on A r x = maximum_on A r x"
  apply (simp add: strict_linear_order_on_def irrefl_def total_on_def trans_def maximal_on_def maximum_on_def upper_bound_on_def)
  by blast

lemma strict_partial_order_on_finite_non_empty_set_has_maximal :
  "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x)"
proof - 
  have "\<And>n. strict_partial_order r \<Longrightarrow> (\<forall> A. Suc n = card A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x))"
  proof - 
    assume "strict_partial_order r"
    then have "(\<forall>a. (a, a) \<notin> r)" 
      by (simp add: strict_partial_order_def irrefl_def) 
    fix n
    show "\<forall> A. Suc n = card A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x)"
      apply (induction n)
      unfolding maximal_on_def
      using \<open>(\<forall>a. (a, a) \<notin> r)\<close>
      apply (metis card_eq_SucD empty_iff insert_iff)
    proof -
      fix n
      assume "\<forall>A. Suc n = card A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists>x. x \<in> A \<and> (\<forall>y. (x, y) \<in> r \<longrightarrow> y \<notin> A))"
      have "\<forall>B. Suc (Suc n) = card B \<longrightarrow> finite B \<longrightarrow> B \<noteq> \<emptyset> \<longrightarrow> (\<exists> A' b. B = A' \<union> {b} \<and> card A' = Suc n \<and> b \<notin> A')"
        by (metis Un_commute add_diff_cancel_left' card_gt_0_iff card_insert_disjoint card_le_Suc_iff insert_is_Un not_le not_less_eq_eq plus_1_eq_Suc)
      then have "\<forall>B. Suc (Suc n) = card B \<longrightarrow> finite B \<longrightarrow> B \<noteq> \<emptyset> \<longrightarrow> (\<exists> A' b. B = A' \<union> {b} \<and> card A' = Suc n \<and> finite A' \<and> A' \<noteq> \<emptyset> \<and> b \<notin> A')"
        by (metis card_gt_0_iff zero_less_Suc)
      then have "\<forall>B. Suc (Suc n) = card B \<longrightarrow> finite B \<longrightarrow> B \<noteq> \<emptyset>
          \<longrightarrow> (\<exists> A' b x. B = A' \<union> {b} \<and> b \<notin> A' \<and> x \<in> A' \<and> (\<forall>y. (x, y) \<in> r \<longrightarrow> y \<notin> A'))"
        using \<open>\<forall>A. Suc n = card A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists>x. x \<in> A \<and> (\<forall>y. (x, y) \<in> r \<longrightarrow> y \<notin> A))\<close> 
        by metis
      then show "\<forall>B. Suc (Suc n) = card B \<longrightarrow> finite B \<longrightarrow> B \<noteq> \<emptyset> \<longrightarrow> (\<exists>x. x \<in> B \<and> (\<forall>y. (x, y) \<in> r \<longrightarrow> y \<notin> B))"
        by (metis (no_types, lifting) Un_insert_right \<open>\<forall>a. (a, a) \<notin> r\<close> \<open>strict_partial_order r\<close> insertE insert_iff strict_partial_order_def sup_bot.right_neutral transE)
    qed
  qed
  then show ?thesis
    by (metis card.insert_remove finite.cases)
qed

lemma strict_partial_order_on_finite_non_empty_set_has_maximal :
  "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x)"
  apply (rule, rule, rule)
proof - 
  assume "strict_partial_order r"
  then have "(\<forall>a. (a, a) \<notin> r)" 
    by (simp add: strict_partial_order_def irrefl_def) 
  assume "finite A" 
  assume "A \<noteq> \<emptyset>"
  show "\<exists> x. maximal_on A r x"
    apply (induction "card A - 1")
  proof -
    assume "0 = card A - 1"
    then have "card A = 1"
      by (metis One_nat_def Suc_pred \<open>A \<noteq> \<emptyset>\<close> \<open>finite A\<close> card_gt_0_iff)
    then show "Ex (maximal_on A r)"
      unfolding maximal_on_def
      using \<open>(\<forall>a. (a, a) \<notin> r)\<close>
      by (metis card_1_singletonE insertI1 singletonD)  
  next 
    fix n
    assume "n = card A - 1 \<Longrightarrow> Ex (maximal_on A r)"
    then have "Suc n = card A \<Longrightarrow> (\<exists> x. maximal_on A r x)"
      by simp
    assume "Suc n = card A - 1"
    then have "\<exists> A' x. A = A' \<union> {x} \<and> card A' = Suc n \<and> x \<notin> A'"
      using \<open>A \<noteq> \<emptyset>\<close> \<open>finite A\<close>
      by (metis Un_commute add_diff_cancel_left' card_gt_0_iff card_insert_disjoint card_le_Suc_iff insert_is_Un not_le not_less_eq_eq plus_1_eq_Suc)
    then obtain A' x where "A = A' \<union> {x} \<and> card A' = Suc n \<and> x \<notin> A'"
      by auto
    have "\<exists> x'. maximal_on A' r x'"
      using \<open>Suc n = card A \<Longrightarrow> (\<exists> x. maximal_on A r x)\<close> 
      sorry
    (* Then we do case analysis. *)
    then show "Ex (maximal_on A r)"
      sorry
  qed
qed

lemma strict_partial_order_on_finite_non_empty_set_has_maximal_by_contradiction :
  "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x)"
proof (rule ccontr)
  (* NOTE: How to use \<not> for pure logic? #81 *)
  assume "\<not> (strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x))"
  then have "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> \<not> (\<exists> x. maximal_on A r x)"
    by simp
  then have "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> \<not> (\<exists> x. x \<in> A \<and> (\<forall> y. (x, y) \<in> r \<longrightarrow> y \<notin> A))"
    by (simp add: maximal_on_def) 
  then have "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<forall> x. x \<notin> A \<or> (\<exists> y. (x, y) \<in> r \<and> y \<in> A))"
    by simp 
  then have "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<forall> x \<in> A. (\<exists> y. (x, y) \<in> r \<and> y \<in> A))"
    by simp 
  then show False
    using strict_partial_order_def irrefl_def trans_def
    sorry
qed

lemma strict_partial_order_has_at_most_one_maximum :
  "strict_partial_order r
  \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> 
  \<longrightarrow> is_singleton {x. maximum_on A r x}"
proof (rule ccontr)
  assume "\<not> (strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x})"
  then have "strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> \<not> is_singleton {x. maximum_on A r x}"
    by simp
  then have "strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> (\<exists> x1 x2. x1 \<noteq> x2 \<and> {x1, x2} \<subseteq> {x. maximum_on A r x})"
    by (meson empty_subsetI insert_subset is_singletonI')
  then have "strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> (\<exists> x1 x2. x1 \<noteq> x2 \<and> {x1, x2} \<subseteq> {x \<in> A. \<forall> y. y \<in> A \<longrightarrow> (y, x) \<in> r \<or> x = y})"
    by (simp add: maximum_on_def upper_bound_on_def)
  then have "strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> (\<exists> x1 x2. x1 \<noteq> x2 \<and> {x1, x2} \<subseteq> A \<and> (\<forall> y. y \<in> A \<longrightarrow> (y, x1) \<in> r \<or> x1 = y) \<and> (\<forall> y. y \<in> A \<longrightarrow> (y, x2) \<in> r \<or> x2 = y))"
    by auto
  then show False
    using strict_partial_order_def
    (* NOTE: Why \<open>...\<close> is required? *)
    by (metis \<open>\<not> (strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x})\<close> insert_subset irrefl_def transE)
qed

lemma strict_linear_order_on_finite_non_empty_set_has_one_maximum :
  "strict_linear_order_on A r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x}"
  oops

end