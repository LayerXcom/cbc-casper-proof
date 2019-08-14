theory DiGraph
  imports Main
begin

(* directed graph *)
record ('v,'e) digraph =
  vertices :: "'v set"
  edges :: "'e set"
  source :: "'e \<Rightarrow> 'v"
  target :: "'e \<Rightarrow> 'v"

locale digraph =
  fixes G :: "('v,'e) digraph"
  assumes source_vertex [simp]: "e \<in> edges G \<Longrightarrow> source G e \<in> vertices G"
  and target_vertex [simp]: "e \<in> edges G \<Longrightarrow> target G e \<in> vertices G"

(* Message Graph: DAG mapped on R^2 grid *)
(* In the context of Casper, this graph is constructed from states and messages in it. *)
record 'a binop =
  op :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

locale msgraph =
  fixes G :: "('v \<times> 't, 'e) digraph"
  and L :: "'t binop"
  assumes L_linear_order [simp]: "linear_order {(t1,t2). t1 \<in> snd ` vertices G \<and> t2 \<in> snd ` vertices G \<and> op L t1 t2}"
  and edge_future_to_past: "e \<in> edges G \<Longrightarrow> op L (snd (target G e)) (snd (source G e))"
  and irredundant: "n \<in> vertices G \<Longrightarrow> \<exists>e \<in> edges G. source G e = n \<or> target G e = n"
  and finite: "finite (vertices G)" "finite (edges G)"
begin

definition V where
  "V = fst ` vertices G"

definition edge_hom (infix "\<leadsto>" 80) where
  "edge_hom s t = {e \<in> edges G. source G e = s \<and> target G e = t}"

definition sources where
  "sources = source G ` edges G"

definition targets where
  "targets = target G ` edges G"

abbreviation lin_op (infix "<<" 60) where
  "lin_op \<equiv> op L"

lemma lin_op_refl [simp]: "reflp lin_op"
  using L_linear_order
  by (simp add: linear_order_on_def partial_order_on_def preorder_on_def reflp_def refl_on_def)

lemma lin_op_totality [simp]:
  assumes "x \<in> snd ` vertices G" "y \<in> snd ` vertices G"
  shows "x << y \<or> y << x"
  using assms L_linear_order
  apply (simp add: linear_order_on_def total_on_def)
  by (metis lin_op_refl reflpD)

lemma lin_op_trans [simp]: "\<lbrakk> {x,y,z} \<subseteq> snd ` vertices G; x << y; y << z \<rbrakk> \<Longrightarrow> x << z"
  using L_linear_order
  apply (simp add: linear_order_on_def partial_order_on_def preorder_on_def trans_def)
  by blast

lemma lin_op_antisym: "\<lbrakk> {x,y} \<subseteq> snd ` vertices G; x << y; y << x \<rbrakk> \<Longrightarrow> x = y"
  using L_linear_order
  apply (simp add: linear_order_on_def partial_order_on_def preorder_on_def)
  using antisym_def
  by (metis (mono_tags, lifting) mem_Collect_eq old.prod.case)

definition max where
  "max x y \<equiv> if x << y then y else x"

definition min where
  "min x y \<equiv> if x << y then x else y"

lemma max_prop [simp]:
  assumes "{x,y} \<subseteq> snd ` vertices G"
  shows "x << max x y" "y << max x y"
  apply (simp add: local.max_def reflpD)
  apply (simp add: local.max_def reflpD)
  by (meson assms insert_subset lin_op_totality)

lemma min_prop [simp]:
  assumes "{x,y} \<subseteq> snd ` vertices G"
  shows "min x y << x" "min x y << y"
  apply (simp add: local.min_def reflpD)
  apply (meson assms insert_subset lin_op_totality)
  apply (simp add: local.min_def reflpD)
  done

end

definition (in msgraph) is_maximal_node where
  "is_maximal_node v \<equiv> (\<forall>e \<in> edges G. v \<noteq> target G e)"

definition (in msgraph) node_over where
  "node_over v = {n \<in> vertices G. fst n = v}"

definition (in msgraph) follows where
  "follows n \<equiv> { m. m \<in> node_over (fst n) \<and> snd n << snd m }"

lemma (in msgraph) follows_on_same_fst [elim]: "y \<in> follows x \<Longrightarrow> fst x = fst y"
  by (smt mem_Collect_eq msgraph.follows_def msgraph.node_over_def msgraph_axioms)

inductive (in msgraph) intervalp where
  "\<lbrakk> n1 \<in> vertices G; n2 \<in> follows n1; n3 \<in> follows n1; snd n3 << snd n2 \<rbrakk> \<Longrightarrow> intervalp n1 n2 n3"

abbreviation (in msgraph) interval where
  "interval n1 n2 \<equiv> {n \<in> vertices G. intervalp n1 n2 n}"

lemma (in msgraph) interval_in_follows [simp]: "interval n1 n2 \<subseteq> follows n1"
  using intervalp.cases by blast

lemma (in msgraph) interval_finite [simp]: "finite (interval n1 n2)"
  by (simp add: local.finite(1))

lemma (in msgraph) follows_finite [simp]: "finite (follows n)"
  by (simp add: follows_def local.finite(1) node_over_def)

lemma (in msgraph) interval_has_endpoints [simp]: "\<lbrakk> n1 \<in> vertices G; n2 \<in> follows n1 \<rbrakk> \<Longrightarrow> {n1, n2} \<subseteq> interval n1 n2"
  apply (auto)
  apply (smt intervalp.intros lin_op_refl mem_Collect_eq msgraph.follows_def msgraph.node_over_def msgraph_axioms reflpD)
  apply (metis (no_types, lifting) follows_def mem_Collect_eq node_over_def)
  apply (smt intervalp.intros lin_op_refl mem_Collect_eq msgraph.follows_def msgraph.node_over_def msgraph_axioms reflpD)
  done

lemma (in msgraph) follows_transitive [simp]: "\<lbrakk> x \<in> vertices G; y \<in> follows x; z \<in> follows y \<rbrakk> \<Longrightarrow> z \<in> follows x"
  unfolding follows_def node_over_def
  apply auto
proof-
  assume "x \<in> vertices G" "y \<in> vertices G" "z \<in> vertices G" "fst y = fst x" "snd x << snd y" "fst z = fst x" "snd y << snd z"
  show "snd x << snd z"
    using lin_op_trans
    using \<open>snd x << snd y\<close> \<open>snd y << snd z\<close> \<open>x \<in> vertices G\<close> \<open>y \<in> vertices G\<close> \<open>z \<in> vertices G\<close> by blast
qed

lemma (in msgraph) interval_union [simp]:
  assumes "n1 \<in> vertices G" "n2 \<in> follows n1" "n3 \<in> follows n2"
  shows "interval n1 n2 \<union> interval n2 n3 = interval n1 n3"
proof rule
  have "n3 \<in> follows n1"
    using assms
    by simp

  { fix x
    assume "x \<in> interval n1 n2 \<union> interval n2 n3"
    { assume "x \<in> interval n1 n2"
      hence "n1 \<in> vertices G \<and> n2 \<in> follows n1 \<and> x \<in> follows n1 \<and> snd x << snd n2"
        using intervalp.cases by blast
      hence "n1 \<in> vertices G \<and> n3 \<in> follows n1 \<and> x \<in> follows n1 \<and> snd x << snd n3"
        by (smt assms(3) mem_Collect_eq msgraph.follows_def msgraph.follows_transitive msgraph.node_over_def msgraph_axioms)
    }
    hence "x \<in> interval n1 n3"
      by (metis (no_types, lifting) Un_iff \<open>x \<in> interval n1 n2 \<union> interval n2 n3\<close> assms(1) assms(2) follows_transitive intervalp.cases intervalp.intros mem_Collect_eq)
  }
  thus "interval n1 n2 \<union> interval n2 n3 \<subseteq> interval n1 n3"
    by blast
next
  { fix x
    assume "x \<in> interval n1 n3"
    hence "fst x = fst n1" "fst x = fst n3"
      apply (metis (mono_tags, lifting) follows_def intervalp.cases mem_Collect_eq node_over_def)
      by (metis (mono_tags, lifting) \<open>x \<in> interval n1 n3\<close> follows_def intervalp.cases mem_Collect_eq node_over_def)

    { assume "snd x << snd n2"
      have "n1 \<in> vertices G"
        using assms by simp
      moreover have "n2 \<in> follows n1"
        using assms by simp
      moreover have "x \<in> follows n1"
        using \<open>x \<in> interval n1 n3\<close> intervalp.cases by blast
      ultimately have "x \<in> interval n1 n2"
        using \<open>snd x << snd n2\<close> \<open>x \<in> interval n1 n3\<close> intervalp.intros by blast
    }
    hence "snd x << snd n2 \<Longrightarrow> x \<in> interval n1 n2"
      by simp

    { assume "snd n2 << snd x"
      have "n2 \<in> vertices G"
        using assms(2) follows_def node_over_def by auto
      moreover have "n3 \<in> follows n2"
        using assms by simp
      moreover have "x \<in> follows n2"
        by (metis (no_types, lifting) \<open>snd n2 << snd x\<close> \<open>x \<in> interval n1 n3\<close> calculation(2) follows_def follows_on_same_fst intervalp.cases mem_Collect_eq)
      ultimately have "x \<in> interval n2 n3"
        by (metis (no_types, lifting) \<open>x \<in> interval n1 n3\<close> intervalp.cases mem_Collect_eq msgraph.intervalp.intros msgraph_axioms)
    }
    hence "snd n2 << snd x \<Longrightarrow> x \<in> interval n2 n3"
      by simp

    have "x \<in> interval n1 n2 \<union> interval n2 n3"
      by (metis (no_types, lifting) UnI1 UnI2 \<open>snd n2 << snd x \<Longrightarrow> x \<in> interval n2 n3\<close> \<open>snd x << snd n2 \<Longrightarrow> x \<in> interval n1 n2\<close> \<open>x \<in> interval n1 n3\<close> assms(1) assms(2) image_eqI insert_subset interval_has_endpoints lin_op_totality mem_Collect_eq)
  }
  thus "interval n1 n3 \<subseteq> interval n1 n2 \<union> interval n2 n3"
    by blast
qed

lemma (in msgraph) interval_split: "x \<in> interval n1 n2 \<Longrightarrow> interval n1 n2 = interval n1 x \<union> interval x n2"
proof-
  assume "x \<in> interval n1 n2"
  have "n1 \<in> vertices G"
    using \<open>x \<in> interval n1 n2\<close> intervalp.cases by blast
  moreover have "x \<in> follows n1"
    using \<open>x \<in> interval n1 n2\<close> intervalp.cases by blast
  moreover have "n2 \<in> follows x"
    by (metis (mono_tags, lifting) \<open>x \<in> interval n1 n2\<close> follows_def follows_on_same_fst intervalp.cases mem_Collect_eq)
  ultimately show "interval n1 n2 = interval n1 x \<union> interval x n2"
    by (simp add: \<open>x \<in> follows n1\<close>)
qed

lemma (in msgraph) follows_split_with_interval: "\<lbrakk> x \<in> vertices G; y \<in> follows x \<rbrakk> \<Longrightarrow> follows x = interval x y \<union> follows y"
proof-
  assume "x \<in> vertices G" "y \<in> follows x"
  { fix z
    assume "z \<in> follows x" and "snd z << snd y"
    hence "z \<in> interval x y"
      by (smt Un_iff \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> in_mono insert_is_Un intervalp.intros mem_Collect_eq msgraph.interval_has_endpoints msgraph_axioms singletonI)
  }
  hence "\<And>z. snd z << snd y \<Longrightarrow> z \<in> follows x \<Longrightarrow> z \<in> interval x y \<union> follows y" by blast

  { fix z
    assume "z \<in> follows x" and "snd y << snd z"
    hence "z \<in> follows y"
      by (metis (mono_tags, lifting) \<open>y \<in> follows x\<close> follows_def follows_on_same_fst mem_Collect_eq)
  }
  hence "\<And>z. snd y << snd z \<Longrightarrow> z \<in> follows x \<Longrightarrow> z \<in> interval x y \<union> follows y" by blast
  have "follows x \<subseteq> interval x y \<union> follows y"
    apply (rule)
    by (metis (no_types, lifting) \<open>\<And>z. \<lbrakk>snd y << snd z; z \<in> follows x\<rbrakk> \<Longrightarrow> z \<in> interval x y \<union> follows y\<close> \<open>\<And>z. \<lbrakk>snd z << snd y; z \<in> follows x\<rbrakk> \<Longrightarrow> z \<in> interval x y \<union> follows y\<close> \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> image_eqI insert_subset interval_has_endpoints mem_Collect_eq msgraph.lin_op_totality msgraph_axioms)

  have "\<And>z. z \<in> interval x y \<union> follows y \<Longrightarrow> z \<in> follows x"
    by (metis (no_types, lifting) Un_iff \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> follows_transitive intervalp.cases mem_Collect_eq)

  show "follows x = interval x y \<union> follows y"
    by (simp add: \<open>\<And>z. z \<in> interval x y \<union> follows y \<Longrightarrow> z \<in> follows x\<close> \<open>follows x \<subseteq> interval x y \<union> follows y\<close> subsetI subset_antisym)
qed

lemma (in msgraph) follows_interval_intersection: "\<lbrakk> x \<in> vertices G; y \<in> follows x \<rbrakk> \<Longrightarrow> interval x y \<inter> follows y = {y}"
  apply rule
  defer
  apply (metis (no_types, lifting) Int_Collect follows_def insert_subset interval_has_endpoints lin_op_refl mem_Collect_eq msgraph.follows_on_same_fst msgraph_axioms reflpD singletonD subsetI)
proof-
  assume "x \<in> vertices G" "y \<in> follows x"
  { fix z
    assume "z \<in> interval x y \<inter> follows y"
    hence "snd z << snd y" "snd y << snd z"
      apply (metis (no_types, lifting) Int_lower1 intervalp.cases mem_Collect_eq subset_iff)
      using \<open>z \<in> interval x y \<inter> follows y\<close> follows_def by auto
    hence "snd y = snd z"
      by (metis (no_types, lifting) IntD1 \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> \<open>z \<in> interval x y \<inter> follows y\<close> empty_subsetI image_eqI insert_subset interval_has_endpoints lin_op_antisym mem_Collect_eq)
    hence "y = z"
      by (meson Int_lower2 \<open>z \<in> interval x y \<inter> follows y\<close> follows_on_same_fst prod_eqI subsetD)
  }
  thus "interval x y \<inter> follows y \<subseteq> {y}"
    by blast
qed

lemma (in msgraph) follows_interval_card: "\<lbrakk> x \<in> vertices G; y \<in> follows x \<rbrakk> \<Longrightarrow> Suc (card (follows x)) = card (interval x y) + card (follows y)"
proof-
  assume "x \<in> vertices G" "y \<in> follows x"
  have "follows x = interval x y \<union> follows y" "interval x y \<inter> follows y = {y}"
    using \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> follows_split_with_interval apply blast
    by (simp add: \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> follows_interval_intersection)

  have p: "follows x = interval x y \<union> (follows y - {y})"
    using \<open>follows x = interval x y \<union> follows y\<close> \<open>interval x y \<inter> follows y = {y}\<close> by fastforce
  have "interval x y \<inter> (follows y - {y}) = {}"
    using \<open>interval x y \<inter> follows y = {y}\<close> by auto
  hence "card (follows x) = card (interval x y) + card (follows y - {y})"
    apply (subst p)
    by (simp add: card_Un_disjoint)
  thus "Suc (card (follows x)) = card (interval x y) + card (follows y)"
    by (metis (no_types, lifting) IntD1 Int_commute \<open>interval x y \<inter> follows y = {y}\<close> add_Suc_right card.remove follows_finite insertI1)
qed

definition (in msgraph) adjacent where
  "adjacent n1 n2 \<equiv> (interval n1 n2 = {n1, n2})"

definition (in msgraph) mg_honest :: "('v \<times> 't) \<Rightarrow> ('v \<times> 't) \<Rightarrow> bool" where
  "mg_honest n1 n2 \<equiv> adjacent n1 n2 \<longrightarrow> (\<exists>e \<in> edges G. e \<in> n2 \<leadsto> n1)"

abbreviation (in msgraph) mg_equivocation where
  "mg_equivocation n1 n2 \<equiv> \<not> mg_honest n1 n2"

definition (in msgraph) mg_equivocations where
  "mg_equivocations = {(n1,n2). n1 \<in> vertices G \<and> n2 \<in> vertices G \<and> mg_equivocation n1 n2}"

abbreviation (in msgraph) mg_non_equivocating where
  "mg_non_equivocating \<equiv> (mg_equivocations = {})"

lemma (in msgraph) non_equivocating_all_honest [simp]:
  assumes "mg_non_equivocating" "adjacent n1 n2" "n1 \<in> vertices G" "n2 \<in> vertices G"
  obtains e where "e \<in> edges G" "e \<in> n2 \<leadsto> n1"
  using assms
  apply (simp add: mg_equivocations_def mg_honest_def)
  by (metis prod.collapse)

lemma set_destruct_by_card:
  assumes "card X = Suc n"
  obtains x xs where "X = {x} \<union> xs" "card xs = n"
  using assms card_eq_SucD that by auto

lemma (in msgraph) non_adjacent_has_intermediate_element [simp]:
  assumes "n1 \<in> vertices G" "n2 \<in> follows n1" "\<not> adjacent n1 n2"
  obtains n3 where "n3 \<in> interval n1 n2" "n3 \<notin> {n1, n2}"
  by (metis (mono_tags, lifting) adjacent_def assms(1) assms(2) assms(3) interval_has_endpoints subsetI subset_antisym)

definition (in msgraph) latest where
  "latest n = (follows n = {n})"

lemma (in msgraph) latest_is_maximal_in_snd: "\<lbrakk> x \<in> vertices G; latest y; y \<in> follows x \<rbrakk> \<Longrightarrow> (\<And>z. z \<in> follows x \<Longrightarrow> snd z << snd y)"
proof-
  { fix z
    assume "x \<in> vertices G" "latest y" "y \<in> follows x" "z \<in> follows x"
    have "snd y << snd z \<Longrightarrow> z \<in> follows y"
      by (metis (mono_tags, lifting) \<open>y \<in> follows x\<close> \<open>z \<in> follows x\<close> follows_def follows_on_same_fst mem_Collect_eq)
    hence "snd y << snd z \<Longrightarrow> z = y"
      using \<open>latest y\<close> latest_def by blast
    hence "snd y << snd z \<Longrightarrow> snd z << snd y"
      by blast
    hence "snd z << snd y"
      using lin_op_totality
      by (metis (no_types, lifting) IntD1 \<open>x \<in> vertices G\<close> \<open>y \<in> follows x\<close> \<open>z \<in> follows x\<close> follows_interval_intersection image_eqI mem_Collect_eq singletonI)
  }
  thus "x \<in> vertices G \<Longrightarrow> latest y \<Longrightarrow> y \<in> follows x \<Longrightarrow> (\<And>z. z \<in> follows x \<Longrightarrow> snd z << snd y)"
    by blast
qed

lemma (in msgraph) follows_as_interval_by_latest: "\<lbrakk> x \<in> vertices G; latest y; y \<in> follows x \<rbrakk> \<Longrightarrow> follows x = interval x y"
  by (metis (no_types, lifting) Un_commute follows_split_with_interval insert_subset interval_has_endpoints latest_def subset_Un_eq)

lemma (in msgraph) exist_linorder_Max:
  assumes "X \<noteq> {}" "finite X" "X \<subseteq> snd ` vertices G"
  obtains y where "y \<in> X" "\<And>x. x \<in> X \<Longrightarrow> x << y"
proof-
  {
    fix n
    have "\<lbrakk> card X = n; X \<noteq> {}; finite X; X \<subseteq> snd ` vertices G \<rbrakk> \<Longrightarrow> \<exists>y \<in> X. (\<forall>x \<in> X. x << y)"
      apply (induct n arbitrary: X)
       apply simp
    proof-
      fix n :: nat and X :: "'t set"
      assume "(\<And>X. card X = n \<Longrightarrow> X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> X \<subseteq> snd ` vertices G \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. x << y)"
        and "card X = Suc n" "X \<noteq> {}" "finite X" "X \<subseteq> snd ` vertices G"
      obtain x xs where "X = {x} \<union> xs" "card xs = n"
        using \<open>card X = Suc n\<close> set_destruct_by_card by blast
      { assume "xs = {}"
        hence "X = {x}"
          using \<open>X = {x} \<union> xs\<close> by auto
        hence "\<exists>y\<in>X. \<forall>x\<in>X. x << y"
          by (simp add: reflpD)
      }
      hence "xs = {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. x << y" by simp

      { assume "xs \<noteq> {}"
        obtain y where "y \<in> xs" "\<forall>z \<in> xs. z << y"
          using \<open>X = {x} \<union> xs\<close> \<open>X \<subseteq> snd ` vertices G\<close> \<open>\<And>X. \<lbrakk>card X = n; X \<noteq> {}; finite X; X \<subseteq> snd ` vertices G\<rbrakk> \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. x << y\<close> \<open>card xs = n\<close> \<open>finite X\<close> \<open>xs \<noteq> {}\<close> by blast
        hence "\<And>z. z \<in> X \<Longrightarrow> z << max x y"
        proof-
          fix z
          assume "z \<in> X"
          hence "z \<in> {x} \<Longrightarrow> z << max x y"
            by (metis lin_op_refl local.max_def reflpD singletonD)
          moreover have "z \<in> xs \<Longrightarrow> z << max x y"
            using lin_op_trans
            by (smt \<open>X = {x} \<union> xs\<close> \<open>X \<subseteq> snd ` vertices G\<close> \<open>\<forall>z\<in>xs. z << y\<close> \<open>y \<in> xs\<close> insert_subset le_sup_iff lin_op_totality local.max_def mk_disjoint_insert)
          ultimately show "z << max x y"
            using \<open>X = {x} \<union> xs\<close> \<open>z \<in> X\<close> by blast
        qed
        hence "\<exists>y\<in>X. \<forall>x\<in>X. x << y"
          by (metis Un_iff \<open>X = {x} \<union> xs\<close> \<open>y \<in> xs\<close> insertI1 insert_is_Un local.max_def)
      }
      hence "xs \<noteq> {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. x << y"
        by simp

      show "\<exists>y\<in>X. \<forall>x\<in>X. x << y"
        using \<open>xs = {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. x << y\<close> \<open>xs \<noteq> {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. x << y\<close> by blast
    qed
  }

  thus "(\<And>y. y \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x << y) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using assms
    by meson
qed

lemma (in msgraph) exist_linorder_Min:
  assumes "X \<noteq> {}" "finite X" "X \<subseteq> snd ` vertices G"
  obtains y where "y \<in> X" "\<And>x. x \<in> X \<Longrightarrow> y << x"
proof-
  {
    fix n
    have "\<lbrakk> card X = n; X \<noteq> {}; finite X; X \<subseteq> snd ` vertices G \<rbrakk> \<Longrightarrow> \<exists>y \<in> X. (\<forall>x \<in> X. y << x)"
      apply (induct n arbitrary: X)
       apply simp
    proof-
      fix n :: nat and X :: "'t set"
      assume "(\<And>X. card X = n \<Longrightarrow> X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> X \<subseteq> snd ` vertices G \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. y << x)"
        and "card X = Suc n" "X \<noteq> {}" "finite X" "X \<subseteq> snd ` vertices G"
      obtain x xs where "X = {x} \<union> xs" "card xs = n"
        using \<open>card X = Suc n\<close> set_destruct_by_card by blast
      { assume "xs = {}"
        hence "X = {x}"
          using \<open>X = {x} \<union> xs\<close> by auto
        hence "\<exists>y\<in>X. \<forall>x\<in>X. y << x"
          by (simp add: reflpD)
      }
      hence "xs = {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. y << x" by simp

      { assume "xs \<noteq> {}"
        obtain y where "y \<in> xs" "\<forall>z \<in> xs. y << z"
          using \<open>X = {x} \<union> xs\<close> \<open>X \<subseteq> snd ` vertices G\<close> \<open>\<And>X. \<lbrakk>card X = n; X \<noteq> {}; finite X; X \<subseteq> snd ` vertices G\<rbrakk> \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. y << x\<close> \<open>card xs = n\<close> \<open>finite X\<close> \<open>xs \<noteq> {}\<close> by blast
        hence "\<And>z. z \<in> X \<Longrightarrow> min x y << z"
        proof-
          fix z
          assume "z \<in> X"
          hence "z \<in> {x} \<Longrightarrow> min x y << z"
            by (metis (no_types, lifting) \<open>X = {x} \<union> xs\<close> \<open>X \<subseteq> snd ` vertices G\<close> \<open>y \<in> xs\<close> insertCI insert_is_Un lin_op_totality local.min_def singletonD subset_iff)
          moreover have "z \<in> xs \<Longrightarrow> min x y << z"
            using lin_op_trans
            by (smt \<open>X = {x} \<union> xs\<close> \<open>X \<subseteq> snd ` vertices G\<close> \<open>\<forall>z\<in>xs. y << z\<close> \<open>y \<in> xs\<close> insert_subset le_sup_iff lin_op_totality local.min_def mk_disjoint_insert)
          ultimately show "min x y << z"
            using \<open>X = {x} \<union> xs\<close> \<open>z \<in> X\<close> by blast
        qed
        hence "\<exists>y\<in>X. \<forall>x\<in>X. y << x"
          by (metis Un_iff \<open>X = {x} \<union> xs\<close> \<open>y \<in> xs\<close> insertI1 insert_is_Un local.min_def)
      }
      hence "xs \<noteq> {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. y << x"
        by simp

      show "\<exists>y\<in>X. \<forall>x\<in>X. y << x"
        using \<open>xs = {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. y << x\<close> \<open>xs \<noteq> {} \<Longrightarrow> \<exists>y\<in>X. \<forall>x\<in>X. y << x\<close> by blast
    qed
  }

  thus "(\<And>y. y \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> y << x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using assms
    by meson
qed

lemma (in msgraph) follows_has_latest:
  assumes "x \<in> vertices G"
  obtains y where "latest y" "y \<in> follows x"
proof-
  have "finite (follows x)"
    by simp
  moreover have "follows x \<noteq> {}"
    by (smt assms insert_absorb insert_not_empty lin_op_refl mem_Collect_eq msgraph.follows_def msgraph.node_over_def msgraph_axioms reflpD)
  moreover have "follows x \<subseteq> vertices G"
    by (simp add: follows_def node_over_def)
  ultimately obtain sy where "sy \<in> snd ` follows x" "\<And>z. z \<in> snd ` follows x \<Longrightarrow> z << sy"
    by (metis (no_types, hide_lams) empty_is_image exist_linorder_Max finite_imageI subset_image_iff)
  
  have "(fst x, sy) \<in> follows x"
    by (metis (no_types, lifting) \<open>sy \<in> snd ` follows x\<close> imageE msgraph.follows_on_same_fst msgraph_axioms surjective_pairing)
  moreover have "latest (fst x, sy)"
    apply (simp add: latest_def)
    apply rule
    defer
    apply (metis (no_types, lifting) Int_lower2 \<open>(fst x, sy) \<in> follows x\<close> assms follows_interval_intersection)
  proof-
    have "follows (fst x, sy) \<subseteq> follows x"
      using \<open>(fst x, sy) \<in> follows x\<close> assms follows_transitive by blast

    { fix z
      assume "z \<in> follows (fst x, sy)"
      hence "sy << snd z"
        by (simp add: msgraph.follows_def msgraph_axioms)

      hence "z \<in> follows x"
        using \<open>follows (fst x, sy) \<subseteq> follows x\<close> \<open>z \<in> follows (fst x, sy)\<close> by blast
      hence "snd x << snd z"
        using follows_def by blast
      hence "snd z \<in> snd ` follows x"
        using \<open>z \<in> follows x\<close> by blast
      hence "snd z << sy"
        using \<open>\<And>z. z \<in> snd ` follows x \<Longrightarrow> z << sy\<close> by blast
      hence "snd z = sy"
        using lin_op_antisym
        using \<open>follows x \<subseteq> vertices G\<close> \<open>sy << snd z\<close> \<open>sy \<in> snd ` follows x\<close> \<open>z \<in> follows x\<close> by blast
      hence "z = (fst x, sy)"
        using \<open>z \<in> follows x\<close> follows_on_same_fst by auto
    }
    thus "follows (fst x, sy) \<subseteq> {(fst x, sy)}"
      by blast
  qed
  ultimately show "(\<And>y. latest y \<Longrightarrow> y \<in> follows x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by blast
qed

lemma (in msgraph) follows_as_interval:
  assumes "x \<in> vertices G"
  obtains y where "latest y" "follows x = interval x y"
  by (metis (no_types, lifting) assms follows_as_interval_by_latest follows_has_latest)

lemma measure_induct_rule_Suc:
  fixes n :: nat
  assumes "P 0"
  and "\<And>n. (\<And>k. k \<le> n \<Longrightarrow> P k) \<Longrightarrow> P (Suc n)"
  shows "P n"
  using assms
  by (metis full_nat_induct not_less_eq_eq old.nat.exhaust)

lemma (in msgraph) node_over_contains_neighbor:
  assumes "s \<in> vertices G" "card (follows s) \<ge> 2"
  obtains m where "adjacent s m"
proof-
  obtain t where "latest t" "follows s = interval s t"
    using assms(1) follows_as_interval by blast

  have "card (interval s t) \<ge> 2"
    using assms
    by (simp add: \<open>follows s = interval s t\<close>)
  hence "s \<noteq> t"
    using \<open>follows s = interval s t\<close> \<open>latest t\<close> latest_def by fastforce
  hence "interval s t - {s} \<noteq> {}"
    by (metis (no_types, lifting) Diff_empty Diff_insert0 One_nat_def Suc_1 Suc_le_mono \<open>2 \<le> card (interval s t)\<close> \<open>follows s = interval s t\<close> card_0_eq card_insert_disjoint empty_iff finite_Diff follows_finite insert_Diff le_0_eq nat.simps(3))
  moreover have "finite (snd ` (interval s t - {s}))"
    by simp
  moreover have "snd ` (interval s t - {s}) \<subseteq> snd ` vertices G"
    by blast
  ultimately obtain uy where "uy \<in> snd ` (interval s t - {s})" "\<And>k. k \<in> snd ` (interval s t - {s}) \<Longrightarrow> uy << k"
    by (meson exist_linorder_Min image_is_empty)

  have "(fst s, uy) \<in> interval s t"
    by (smt DiffD1 \<open>follows s = interval s t\<close> \<open>uy \<in> snd ` (interval s t - {s})\<close> follows_on_same_fst imageE prod.collapse)
  hence "interval s t = interval s (fst s, uy) \<union> interval (fst s, uy) t"
    using interval_split by blast
  moreover have "interval s (fst s, uy) = {s, (fst s, uy)}"
  proof
    { fix x
      assume "x \<in> interval s (fst s, uy)"
      hence "snd s << snd x" "snd x << uy"
        using \<open>follows s = interval s t\<close> calculation follows_def apply auto[1]
        by (metis (no_types, lifting) \<open>x \<in> interval s (fst s, uy)\<close> intervalp.cases mem_Collect_eq snd_conv)
      { assume "s \<noteq> x"
        hence "x \<in> interval s t - {s}"
          using \<open>x \<in> interval s (fst s, uy)\<close> calculation by blast
        hence "uy << snd x"
          using \<open>\<And>k. k \<in> snd ` (interval s t - {s}) \<Longrightarrow> uy << k\<close> by blast
        hence "x = (fst s, uy)"
          by (metis (no_types, lifting) DiffD1 \<open>follows s = interval s t\<close> \<open>snd ` (interval s t - {s}) \<subseteq> snd ` vertices G\<close> \<open>snd x << uy\<close> \<open>uy \<in> snd ` (interval s t - {s})\<close> \<open>x \<in> interval s t - {s}\<close> fst_conv image_eqI insert_is_Un le_sup_iff lin_op_antisym mk_disjoint_insert msgraph.follows_on_same_fst msgraph_axioms prod_eqI snd_conv)
      }
      hence "s \<noteq> x \<Longrightarrow> x \<in> {s, (fst s, uy)}"
        by blast
      hence "x \<in> {s, (fst s, uy)}"
        by blast
    }
    thus "interval s (fst s, uy) \<subseteq> {s, (fst s, uy)}" by blast
  next
    show "{s, (fst s, uy)} \<subseteq> interval s (fst s, uy)"
      using \<open>(fst s, uy) \<in> interval s t\<close> \<open>follows s = interval s t\<close> assms(1) interval_has_endpoints by blast
  qed
  ultimately have "adjacent s (fst s, uy)"
    by (simp add: adjacent_def)
  thus "(\<And>m. adjacent s m \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by blast
qed

lemma (in msgraph) "\<lbrakk> mg_non_equivocating; n \<in> vertices G \<rbrakk> \<Longrightarrow> n \<in> targets \<or> latest n"
  sorry

(* Multi-target directed graph *)
record ('v,'e) tdigraph =
  vertices :: "'v set"
  edges :: "'e set"
  source :: "'e \<Rightarrow> 'v"
  targets :: "'e \<Rightarrow> 'v set"

locale tdigraph =
  fixes G :: "('v,'e) tdigraph"
  assumes source_vertex [simp]: "e \<in> edges G \<Longrightarrow> source G e \<in> vertices G"
  and target_vertex [simp]: "e \<in> edges G \<Longrightarrow> targets G e \<subseteq> vertices G"

fun tdigraph_to_digraph :: "('v,'e) tdigraph \<Rightarrow> ('v, 'e \<times> 'v) digraph" where
  "tdigraph_to_digraph tg = \<lparr> digraph.vertices = vertices tg, edges = {(e,t). e \<in> edges tg \<and> t \<in> targets tg e}, source = (\<lambda>(e,t). source tg e), target = (\<lambda>(e,t). t) \<rparr>"

lemma "tdigraph tg \<Longrightarrow> digraph (tdigraph_to_digraph tg)"
  apply (simp add: digraph_def, auto)
  apply (simp add: tdigraph.source_vertex)
  by (meson subsetD tdigraph.target_vertex)

end
