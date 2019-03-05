theory TFGCasper

imports Main HOL.Real CBCCasper LatestMessage SafetyOracle ConsensusSafety

begin

(* Section 4.4: Casper the Friendly GHOST *)
(* Definition 4.23: Blocks *)
type_synonym block = consensus_value

locale GhostParams = Params +
  (* Definition 4.23: Previous block resolver *)
  fixes B :: "block set"
  fixes genesis :: block
  (* Definition 4.24: Previous block resolver *)
  and prev :: "block \<Rightarrow> block"

(* Definition 4.25: n'th generation ancestor block *)
fun (in GhostParams) n_cestor :: "block * nat \<Rightarrow> block"
  where
    "n_cestor (b, 0) = b"
  | "n_cestor (b, n) = n_cestor (prev b, n-1)"

(* Definition 4.26: Blockchain membership *)
definition (in GhostParams) blockchain_membership :: "block \<Rightarrow> block \<Rightarrow> bool" (infixl "\<downharpoonright>" 70)
  where
    "b1 \<downharpoonright> b2 = (\<exists> n. n \<in> \<nat> \<and> b1 = n_cestor (b2, n))"

notation (ASCII)
  comp  (infixl "blockchain_membership" 70)

(* Definition 4.27: Score of a block *)
definition (in GhostParams) score :: "state \<Rightarrow> block \<Rightarrow> real"
  where
    "score \<sigma> b = sum W {v \<in> observed \<sigma>. \<exists> b' \<in> B. b' \<in> (latest_estimates_from_non_equivocating_validators \<sigma> v) \<and> (b \<downharpoonright> b')}"

(* Definition 4.28: Children *)
definition (in GhostParams) children :: "block * state \<Rightarrow> block set"
  where
    "children = (\<lambda>(b, \<sigma>). {b' \<in> est `\<sigma>. b = prev b'})"

(* Definition 4.29: Best Children *)
definition (in GhostParams) best_children :: "block * state \<Rightarrow>  block set"
  where
    "best_children = (\<lambda> (b, \<sigma>). {arg_max_on (score \<sigma>) (children (b, \<sigma>))})"

(* Definition 4.30: GHOST *)
(* NOTE: well-sortedness error occurs in code generation *)
function (in GhostParams) GHOST :: "(block set * state) => block set"
  where
    "GHOST (b_set, \<sigma>) =
      (\<Union> b \<in> {b \<in> b_set. children (b, \<sigma>) \<noteq> \<emptyset>}. GHOST (best_children (b, \<sigma>), \<sigma>))
       \<union> {b \<in> b_set. children (b, \<sigma>) = \<emptyset>}"
  by auto

(* Definition 4.31: Casper the Friendly Ghost *)
definition (in GhostParams) GHOST_estimator :: "state \<Rightarrow> block set"
  where
    "GHOST_estimator \<sigma> = GHOST ({genesis}, \<sigma>) \<union> (\<Union> b \<in> GHOST ({genesis}, \<sigma>). children (b, \<sigma>))"

(* Definition 4.32: Example non-trivial properties of consensus values *)
abbreviation (in GhostParams) P :: "consensus_value_property set"
  where
    "P \<equiv> {p. \<exists>!b \<in> B. \<forall>b' \<in> B. (b \<downharpoonright> b' \<longrightarrow> p b' = True) \<and> \<not> (b \<downharpoonright> b' \<longrightarrow> p b' = False)}"

(* Locale for proofs *)
locale Blockchain = GhostParams + Protocol +
  assumes blockchain_type : "\<forall> b b' b''. {b, b', b''} \<subseteq> B \<longrightarrow> b' \<downharpoonright> b \<and> b'' \<downharpoonright> b \<longrightarrow> (b' \<downharpoonright> b'' \<or> b'' \<downharpoonright> b')"
  and block_is_consensus_value : "B = C"

definition (in GhostParams) block_finalized_property :: "block \<Rightarrow> consensus_value_property"
  where
    "block_finalized_property b = (\<lambda>b'. b \<downharpoonright> b')"

definition (in GhostParams) block_conflicting :: "(block * block) \<Rightarrow> bool"
  where
    "block_conflicting = (\<lambda>(b1, b2). \<not> (b1 \<downharpoonright> b2 \<or> b2 \<downharpoonright> b1))"

lemma (in Blockchain) conflicting_blocks_imps_conflicting_decision :
  "\<forall> b1 b2 \<sigma>. {b1, b2} \<subseteq> B \<and> \<sigma> \<in> \<Sigma> 
    \<longrightarrow> block_conflicting (b1, b2) 
    \<longrightarrow> consensus_value_property_is_decided (block_finalized_property b1, \<sigma>) 
    \<longrightarrow> consensus_value_property_is_decided (consensus_value_property_not (block_finalized_property b2), \<sigma>)"
  apply (simp add: block_finalized_property_def consensus_value_property_is_decided_def
          naturally_corresponding_state_property_def  state_property_is_decided_def)
  apply (rule, rule, rule, rule, rule, rule) 
proof -
  fix b1 b2 \<sigma>
  assume "b1 \<in> B \<and> b2 \<in> B \<and> \<sigma> \<in> \<Sigma>" and "block_conflicting (b1, b2)" and "\<forall>\<sigma>\<in>futures \<sigma>. \<forall>b'\<in>\<epsilon> \<sigma>. b1 \<downharpoonright> b'" 
  show  "\<forall>\<sigma>\<in>futures \<sigma>. \<forall>c\<in>\<epsilon> \<sigma>. \<not> b2 \<downharpoonright> c"
  proof (rule ccontr)
    assume "\<not> (\<forall>\<sigma>\<in>futures \<sigma>. \<forall>c\<in>\<epsilon> \<sigma>. \<not> b2 \<downharpoonright> c)"
    hence "\<exists> \<sigma> \<in>futures \<sigma>. \<exists> c \<in> \<epsilon> \<sigma>. b2 \<downharpoonright> c"
      by blast
    hence "\<exists> \<sigma> \<in>futures \<sigma>. \<exists> c \<in> \<epsilon> \<sigma>. b2 \<downharpoonright> c \<and> b1 \<downharpoonright> c"
      using \<open>\<forall>\<sigma>\<in>futures \<sigma>. \<forall>b'\<in>\<epsilon> \<sigma>. b1 \<downharpoonright> b'\<close> by simp
    hence "b1 \<downharpoonright> b2 \<or> b2 \<downharpoonright> b1"
      using blockchain_type 
      apply (simp)
      using \<Sigma>t_is_subset_of_\<Sigma> \<open>b1 \<in> B \<and> b2 \<in> B \<and> \<sigma> \<in> \<Sigma>\<close> block_is_consensus_value estimates_are_subset_of_C futures_def by blast
    then show False
      using \<open>block_conflicting (b1, b2)\<close>
      by (simp add: block_conflicting_def)
  qed
qed

theorem (in Blockchain) blockchain_safety :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> (\<forall> \<sigma> \<sigma>' b1 b2. {\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> B \<and> block_conflicting (b1, b2) \<and> block_finalized_property b1 \<in> consensus_value_property_decisions \<sigma> 
      \<longrightarrow> block_finalized_property b2 \<notin> consensus_value_property_decisions \<sigma>')"
  apply (rule, rule, rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma>_set \<sigma> \<sigma>' b1 b2
   assume "\<sigma>_set \<subseteq> \<Sigma>t" and "finite \<sigma>_set" and "is_faults_lt_threshold (\<Union>\<sigma>_set)" 
   and "{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> B \<and> block_conflicting (b1, b2) \<and> block_finalized_property b1 \<in> consensus_value_property_decisions \<sigma>" 
   and "block_finalized_property b2 \<in> consensus_value_property_decisions \<sigma>'" 
   hence "\<not> consensus_value_property_is_decided (consensus_value_property_not (block_finalized_property b1), \<sigma>')"
      using negation_is_not_decided_by_other_validator \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>finite \<sigma>_set\<close> \<open>is_faults_lt_threshold (\<Union>\<sigma>_set)\<close> apply (simp add: consensus_value_property_decisions_def) 
      using \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> B \<and> block_conflicting (b1, b2) \<and> block_finalized_property b1 \<in> consensus_value_property_decisions \<sigma>\<close> by auto
   have "{b1, b2} \<subseteq> B \<and> \<sigma> \<in> \<Sigma> \<and> block_conflicting (b1, b2)"
     using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> B \<and> block_conflicting (b1, b2) \<and> block_finalized_property b1 \<in> consensus_value_property_decisions \<sigma>\<close> by auto
   hence "consensus_value_property_is_decided (consensus_value_property_not (block_finalized_property b1), \<sigma>')"
     using \<open>block_finalized_property b2 \<in> consensus_value_property_decisions \<sigma>'\<close> conflicting_blocks_imps_conflicting_decision
     apply (simp add: consensus_value_property_decisions_def)
     by (metis \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>finite \<sigma>_set\<close> \<open>is_faults_lt_threshold (\<Union>\<sigma>_set)\<close> \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> B \<and> block_conflicting (b1, b2) \<and> block_finalized_property b1 \<in> consensus_value_property_decisions \<sigma>\<close> conflicting_blocks_imps_conflicting_decision consensus_value_property_decisions_def insert_subset mem_Collect_eq negation_is_not_decided_by_other_validator) 
   then show False
     using \<open>\<not> consensus_value_property_is_decided (consensus_value_property_not (block_finalized_property b1), \<sigma>')\<close> by blast
 qed

(* Locale for proofs *)
locale Ghost = GhostParams + Protocol +
  assumes block_type : "\<forall> b. b \<in> B \<longleftrightarrow> prev b \<in> B"
  and block_is_consensus_value : "B = C"
  and ghost_is_estimator : "\<epsilon> = GHOST_estimator"
  and genesis_type : "genesis \<in> C"

lemma (in Ghost) children_type :
  "\<forall> b \<sigma>. b \<in> B \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  children (b, \<sigma>) \<subseteq> B"
  apply (simp add: children_def)
  using Ghost_axioms Ghost_axioms_def Ghost_def by auto

lemma (in Ghost) best_children_type :
  "\<forall> b \<sigma>. b \<in> B \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  best_children (b, \<sigma>) \<subseteq> B"
  apply (simp add: best_children_def arg_max_on_def arg_max_def is_arg_max_def)
  apply auto 
  oops

lemma (in Ghost) GHSOT_type :
  "\<forall> \<sigma> b_set. \<sigma> \<in> \<Sigma> \<and> b_set \<subseteq> B \<longrightarrow>  GHOST(b_set, \<sigma>) \<subseteq> B"
  oops

lemma (in GhostParams) GHOST_is_valid_estimator : 
  "(\<forall> b. b \<in> B \<longleftrightarrow> prev b \<in> B) \<and> B = C \<and> genesis \<in> C 
  \<Longrightarrow> is_valid_estimator GHOST_estimator"
  apply (simp add: is_valid_estimator_def GhostParams.GHOST_estimator_def)
  oops

lemma (in Ghost) block_membership_property_is_majority_driven :
  "\<forall> p \<in> P. is_majority_driven p"
  apply (simp add: is_majority_driven_def)
  (* by (metis DiffE Pow_iff is_valid_estimator_def \<epsilon>_type block_is_consensus_value subsetCE) *)
  oops

lemma (in Ghost) block_membership_property_is_max_driven :
  "\<forall> p \<in> P. is_max_driven p"
  apply (simp add: is_max_driven_def)
  (* FIXME: Timeout *)
  (* by (metis DiffE Nats_0 ghost_is_estimator) *)
  oops

end
