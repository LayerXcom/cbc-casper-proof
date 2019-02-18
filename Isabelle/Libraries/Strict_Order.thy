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
  apply (simp add: strict_linear_order_on_def irrefl_def maximal_on_def maximum_on_def upper_bound_on_def total_on_def)
  by (metis transE)

lemma strict_partial_order_on_finite_non_empty_set_has_maximal :
  "strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x)"
proof (rule ccontr)
  (* NOTE: How to use \<not> for pure logic? #81 *)
  assume "\<not> (strict_partial_order r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x))"
  moreover have "finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> (\<exists> x. maximal_on A r x) \<longrightarrow> (\<forall> x \<in> A. \<exists> y. (x, y) \<in> r \<longrightarrow> y \<in> A)"
    using maximal_on_def by auto
  ultimately show False
    using strict_partial_order_def irrefl_def trans_def
    sorry
qed

lemma strict_partial_order_has_at_most_one_maximum :
  "strict_partial_order r
  \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> 
  \<longrightarrow> is_singleton {x. maximum_on A r x}"
proof (rule ccontr)
  assume "\<not> (strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x})"
  then have "strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> (\<exists> x1 x2. {x1, x2} \<subseteq> A \<and> x1 \<noteq> x2 \<and> (\<forall> y \<in> A. (y, x1) \<in> r) \<and> (\<forall> y \<in> A. (y, x2) \<in> r))"
    apply (simp add: maximum_on_def upper_bound_on_def is_singleton_def strict_partial_order_def irrefl_def)
    apply auto
    (* sledgehammer *)
  proof -
    fix x :: 'a
    assume a1: "\<forall>a. (a, a) \<notin> r"
    assume a2: "trans r"
    obtain aa :: "'a set \<Rightarrow> 'a" and aaa :: "'a set \<Rightarrow> 'a" where
        f3: "aa (Collect (maximum_on A r)) \<in> Collect (maximum_on A r) \<and> aaa (Collect (maximum_on A r)) \<in> Collect (maximum_on A r) \<and> aa (Collect (maximum_on A r)) \<noteq> aaa (Collect (maximum_on A r))"
      by (meson \<open>\<not> (strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x})\<close> is_singletonI')
  have f4: "\<forall>A r a. maximum_on A r (a::'a) = (a \<in> A \<and> upper_bound_on A r a)"
    using maximum_on_def by blast
    then have f5: "(aaa (Collect (maximum_on A r)), aa (Collect (maximum_on A r))) \<in> r"
      using f3 by (metis (no_types) CollectD upper_bound_on_def)
    have "\<forall>a. a \<notin> A \<or> (a, aaa (Collect (maximum_on A r))) \<in> r \<or> aaa (Collect (maximum_on A r)) = a"
      using f4 f3 by (metis CollectD upper_bound_on_def)
  then show "\<exists>x1. x1 \<in> A \<and> (\<exists>x2. x2 \<in> A \<and> x1 \<noteq> x2 \<and> (\<forall>y\<in>A. (y, x1) \<in> r) \<and> (\<forall>y\<in>A. (y, x2) \<in> r))"
    using f5 f4 f3 a2 a1 by (metis (no_types) CollectD transE)
  qed
  then show False
    using strict_partial_order_def antisym_def
    (* NOTE: Why \<open>...\<close> is required? *)
    using \<open>\<not> (strict_partial_order r \<longrightarrow> {x. maximum_on A r x} \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x})\<close> irrefl_def by fastforce
qed

lemma strict_linear_order_on_finite_non_empty_set_has_one_maximum :
  "strict_linear_order_on A r \<longrightarrow> finite A \<longrightarrow> A \<noteq> \<emptyset> \<longrightarrow> is_singleton {x. maximum_on A r x}"
  oops

end