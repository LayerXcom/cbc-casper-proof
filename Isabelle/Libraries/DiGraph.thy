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

(* Multi-layered Graph *)
record 'a binop =
  op :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

locale mlgraph =
  fixes G :: "('v \<times> 't, 'e) digraph"
  and L :: "'t binop"
  assumes L_linear_order: "linear_order {(t1,t2). t1 \<in> snd ` vertices G \<and> t2 \<in> snd ` vertices G \<and> op L t1 t2}"
  and edge_future_to_past: "e \<in> edges G \<Longrightarrow> op L (snd (target G e)) (snd (source G e))"
  and irredundant: "n \<in> vertices G \<Longrightarrow> \<exists>e \<in> edges G. source G e = n \<or> target G e = n"
begin

definition V where
  "V = fst ` vertices G"

definition lin_op (infix "<<" 60) where
  "lin_op = op L"

definition edge_hom (infix "\<leadsto>" 80) where
  "edge_hom s t = {e \<in> edges G. source G e = s \<and> target G e = t}"

definition sources where
  "sources = source G ` edges G"

definition targets where
  "targets = target G ` edges G"

end

definition (in mlgraph) is_maximal_node where
  "is_maximal_node v \<equiv> (\<forall>e \<in> edges G. v \<noteq> target G e)"

definition (in mlgraph) node_over where
  "node_over v = {n \<in> vertices G. fst n = v}"

definition (in mlgraph) follows where
  "follows n1 n2 \<equiv> n2 \<in> node_over (fst n1) \<and> snd n1 << snd n2 \<and> (\<forall>n \<in> node_over (fst n1). snd n1 << snd n \<and> snd n << snd n2 \<longrightarrow> n = n1 \<or> n = n2)"

definition (in mlgraph) ml_honest :: "('v \<times> 't) \<Rightarrow> ('v \<times> 't) \<Rightarrow> bool" where
  "ml_honest n1 n2 \<equiv> follows n1 n2 \<longrightarrow> (\<exists>e \<in> edges G. e \<in> n2 \<leadsto> n1)"

definition (in mlgraph) ml_equivocation where
  "ml_equivocation n1 n2 \<equiv> \<not> ml_honest n1 n2"

definition (in mlgraph) ml_equivocations where
  "ml_equivocations = {(n1,n2). n1 \<in> vertices G \<and> n2 \<in> vertices G \<and> ml_equivocation n1 n2}"

definition (in mlgraph) latest where
  "latest n = (\<forall>v \<in> node_over (fst n). snd v << snd n)"

lemma (in mlgraph) "\<lbrakk> ml_equivocations = {}; n \<in> vertices G \<rbrakk> \<Longrightarrow> n \<in> targets \<or> latest n"
  sorry

end
