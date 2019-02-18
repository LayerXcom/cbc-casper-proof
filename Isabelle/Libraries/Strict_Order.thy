(*  Title:      Strict_Order
    Author:     Ryuya Nakamura <nrryuya@gmail.com>
    Maintainer: Ryuya Nakamura
    License:    LGPL
*)

theory Strict_Order

imports Main Restricted_Predicates

begin

notation Set.empty ("\<emptyset>")

(* Modified from: https://isabelle.in.tum.de/library/HOL/HOL/Order_Relation.html *)
definition strict_linear_order_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" 
  where 
      "strict_linear_order_on P A \<equiv> po_on P A  \<and> total_on P A"

definition strict_well_order_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" 
  where 
      "strict_well_order_on P A \<equiv> strict_linear_order_on P A  \<and> wfp_on P A"

definition upper_bound_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    (* "upper_bound_on P A x = (\<forall> y \<in> A. P y x)" *)
    "upper_bound_on P A x = (\<forall> y. y \<in> A \<longrightarrow> P y x)"

definition maximum_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "maximum_on P A x = (x \<in> A \<and> upper_bound_on P A x)" 

definition minimal_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "minimal_on P A x = (x \<in> A \<and> (\<forall> y. P y x \<longrightarrow> y \<notin> A))" 

definition maximal_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where 
    "maximal_on P A x = (x \<in> A \<and> (\<forall> y. P x y \<longrightarrow> y \<notin> A))"

lemma "(\<not> A \<or> \<not> B) \<equiv> (A \<longrightarrow> \<not> B)"
  by auto

lemma "(A \<longrightarrow> \<not> B) \<equiv> (B \<longrightarrow> \<not> A)"
  by linarith

lemma "A = True \<longrightarrow> ((\<not> (A \<longrightarrow> B)) = (A \<longrightarrow> \<not> B))"
  by auto

lemma strict_partial_order_has_at_most_one_maximum :
  "po_on P A
  \<longrightarrow> {x. maximum_on P A x} \<noteq> \<emptyset> 
  \<longrightarrow> is_singleton {x. maximum_on P A x}"
proof (rule ccontr)
  assume "\<not> (po_on P A \<longrightarrow> {x. maximum_on P A x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on P A x})"
  then have "po_on P A \<longrightarrow> {x. maximum_on P A x} \<noteq> \<emptyset> \<longrightarrow> (\<exists> x1 x2. {x1, x2} \<subseteq> A \<and> x1 \<noteq> x2 \<and> (\<forall> y \<in> A. P y x1) \<and> (\<forall> y \<in> A. P y x2))"
    apply (simp add: maximum_on_def upper_bound_on_def is_singleton_def)
    apply auto
    by blast
  then show False
    using po_on_imp_antisymp_on antisymp_on_def
    (* The reason why \<open>...\<close> is required would be explored below. *)
    by (metis \<open>\<not> (po_on P A \<longrightarrow> {x. maximum_on P A x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on P A x})\<close> insert_subset)
qed

lemma maximal_and_maximum_coincide_for_total_order :
  "total_on P A \<Longrightarrow> maximal_on P A x = maximum_on P A x"
  oops

lemma "finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on P A x) \<longrightarrow> (\<forall> x \<in> A. \<exists> y. y \<in> A \<and> P x y)"
  apply (simp add:  maximal_on_def) 
  oops

lemma strict_partial_order_on_finite_set_has_maximal :
  "po_on P A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on P A x)"
proof (rule ccontr)
  (* NOTE: How to use \<not> for pure logic? #81 *)
  assume "\<not> (po_on P A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on P A x))"
  have "finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on P A x) \<longrightarrow> (\<forall> x \<in> A. \<exists> y. y \<in> A \<and> P x y)"
    using maximal_on_def sorry 
  show False
    using po_on_def irreflp_on_def transp_on_def 
    sorry
qed

lemma strict_linear_order_on_finite_set_has_one_maximum :
  "strict_linear_order_on P A \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on P A x}"
  oops

end