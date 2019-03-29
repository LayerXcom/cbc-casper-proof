theory TFGCasper

imports Main HOL.Real CBCCasper LatestMessage SafetyOracle ConsensusSafety

begin

(* ###################################################### *)
(* Casper TFG *)
(* ###################################################### *)

(* Section 4.4: Casper the Friendly GHOST *)
locale BlockchainParams = Params +
  fixes genesis :: consensus_value
  (* Definition 4.24: Previous block resolver *)
  and prev :: "consensus_value \<Rightarrow> consensus_value"

(* Definition 4.25: n'th generation ancestor block *)
fun (in BlockchainParams) n_cestor :: "consensus_value * nat \<Rightarrow> consensus_value"
  where
    "n_cestor (b, 0) = b"
  | "n_cestor (b, n) = n_cestor (prev b, n-1)"

(* Definition 4.26: Blockchain membership *)
definition (in BlockchainParams) blockchain_membership :: "consensus_value \<Rightarrow> consensus_value \<Rightarrow> bool" (infixl "\<downharpoonright>" 70)
  where
    "b1 \<downharpoonright> b2 = (\<exists> n. n \<in> \<nat> \<and> b1 = n_cestor (b2, n))"

notation (ASCII)
  comp  (infixl "blockchain_membership" 70)

definition (in BlockchainParams) blockchain_membership_rel :: "consensus_value rel"
  where 
    "blockchain_membership_rel = {(b1, b2). {b1, b2} \<subseteq> C \<and> b1 \<downharpoonright> b2}" 

lemma (in BlockchainParams) n_cestor_transitive :
  "\<forall> n1 n2 x y z. {n1, n2} \<subseteq> \<nat> 
    \<longrightarrow> x = n_cestor (y, n1) 
    \<longrightarrow> y = n_cestor (z, n2)
    \<longrightarrow> x = n_cestor (z, n1 + n2)"
  apply (rule, rule)
proof -
  fix n1 n2
  show "\<forall>x y z. {n1, n2} \<subseteq> \<nat> \<longrightarrow> x = n_cestor (y, n1) \<longrightarrow> y = n_cestor (z, n2) \<longrightarrow> x = n_cestor (z, n1 + n2)"
    apply (induction n2)
    apply simp
    apply (rule, rule, rule, rule, rule, rule)
  proof -
    fix n2 x y z
    assume "\<forall>x y z. {n1, n2} \<subseteq> \<nat> \<longrightarrow> x = n_cestor (y, n1) \<longrightarrow> y = n_cestor (z, n2) \<longrightarrow> x = n_cestor (z, n1 + n2)" 
    assume "{n1, Suc n2} \<subseteq> \<nat>"
    assume "x = n_cestor (y, n1)"
    assume "y = n_cestor (z, Suc n2)"
    then have "y = n_cestor (prev z, n2)"
      by simp
    have "{n1, n2} \<subseteq> \<nat>"
      by (simp add: Nats_def)
    then have "x = n_cestor (prev z, n1 + n2)"
      using \<open>x = n_cestor (y, n1)\<close> \<open>y = n_cestor (prev z, n2)\<close>
            \<open>\<forall>x y z. {n1, n2} \<subseteq> \<nat> \<longrightarrow> x = n_cestor (y, n1) \<longrightarrow> y = n_cestor (z, n2) \<longrightarrow> x = n_cestor (z, n1 + n2)\<close>
      by simp
    then show "x = n_cestor (z, n1 + Suc n2)"
      by simp
  qed
qed

lemma (in BlockchainParams) transitivity_of_blockchain_membership :
  "trans blockchain_membership_rel"
  apply (simp add: trans_def blockchain_membership_rel_def blockchain_membership_def)
  using n_cestor_transitive
  by (metis id_apply of_nat_eq_id of_nat_in_Nats subsetI)

(* Block membership property *)
(* This is Definition 4.32: Example non-trivial properties of consensus values *)
definition (in BlockchainParams) block_membership :: "consensus_value \<Rightarrow> consensus_value_property"
  where
    "block_membership b = (\<lambda>b'. b \<downharpoonright> b')"

lemma (in BlockchainParams) also_agreeing_on_ancestors :
  "\<forall> b b'. {b, b'} \<subseteq> C \<and> b \<downharpoonright> b'
  \<longrightarrow> agreeing (block_membership b', \<sigma>, v) \<longrightarrow> agreeing (block_membership b, \<sigma>, v)"
  apply (simp add: agreeing_def block_membership_def)
  oops

(* Definition 4.27: Score of a block *)
definition (in BlockchainParams) score :: "state \<Rightarrow> consensus_value \<Rightarrow> real"
  where
    "score \<sigma> b = sum W {v \<in> observed \<sigma>. \<exists> b' \<in> C. b' \<in> (L_H_E \<sigma> v) \<and> (b \<downharpoonright> b')}"

(* Definition 4.28: Children *)
definition (in BlockchainParams) children :: "consensus_value * state \<Rightarrow> consensus_value set"
  where
    "children = (\<lambda>(b, \<sigma>). {b' \<in> est `\<sigma>. b = prev b'})"

(* Definition 4.29: Best Children *)
definition (in BlockchainParams) best_children :: "consensus_value * state \<Rightarrow> consensus_value set"
  where
    "best_children = (\<lambda> (b, \<sigma>). {arg_max_on (score \<sigma>) (children (b, \<sigma>))})"

(* Definition 4.30: GHOST *)
(* NOTE: well-sortedness error occurs in code generation *)
function (in BlockchainParams) GHOST :: "(consensus_value set * state) \<Rightarrow> consensus_value set"
  where
    "GHOST (b_set, \<sigma>) =
      (\<Union> b \<in> {b \<in> b_set. children (b, \<sigma>) \<noteq> \<emptyset>}. GHOST (best_children (b, \<sigma>), \<sigma>))
       \<union> {b \<in> b_set. children (b, \<sigma>) = \<emptyset>}"
  by auto

(* Definition 4.31: Casper the Friendly Ghost *)
definition (in BlockchainParams) GHOST_estimator :: "state \<Rightarrow> consensus_value set"
  where
    "GHOST_estimator \<sigma> = GHOST ({genesis}, \<sigma>) \<union> (\<Union> b \<in> GHOST ({genesis}, \<sigma>). children (b, \<sigma>))"



(* Locale for proofs *)
locale Blockchain = BlockchainParams + Protocol +
  assumes blockchain_type : "\<forall> b b' b''. {b, b', b''} \<subseteq> C \<longrightarrow> b' \<downharpoonright> b \<and> b'' \<downharpoonright> b \<longrightarrow> (b' \<downharpoonright> b'' \<or> b'' \<downharpoonright> b')"
  and block_is_consensus_value : "C = C"


definition (in BlockchainParams) block_conflicting :: "(consensus_value * consensus_value) \<Rightarrow> bool"
  where
    "block_conflicting = (\<lambda>(b1, b2). \<not> (b1 \<downharpoonright> b2 \<or> b2 \<downharpoonright> b1))"

lemma (in Blockchain) conflicting_blocks_imps_conflicting_decision :
  "\<forall> b1 b2 \<sigma>. {b1, b2} \<subseteq> C \<and> \<sigma> \<in> \<Sigma> 
    \<longrightarrow> block_conflicting (b1, b2) 
    \<longrightarrow> consensus_value_property_is_decided (block_membership b1, \<sigma>) 
    \<longrightarrow> consensus_value_property_is_decided (consensus_value_property_not (block_membership b2), \<sigma>)"
  apply (simp add: block_membership_def consensus_value_property_is_decided_def
          naturally_corresponding_state_property_def  state_property_is_decided_def)
  apply (rule, rule, rule, rule, rule, rule) 
proof -
  fix b1 b2 \<sigma>
  assume "b1 \<in> C \<and> b2 \<in> C \<and> \<sigma> \<in> \<Sigma>" and "block_conflicting (b1, b2)" and "\<forall>\<sigma>\<in>futures \<sigma>. \<forall>b'\<in>\<epsilon> \<sigma>. b1 \<downharpoonright> b'" 
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
      using \<Sigma>t_is_subset_of_\<Sigma> \<open>b1 \<in> C \<and> b2 \<in> C \<and> \<sigma> \<in> \<Sigma>\<close> block_is_consensus_value estimates_are_subset_of_C futures_def by blast
    then show False
      using \<open>block_conflicting (b1, b2)\<close>
      by (simp add: block_conflicting_def)
  qed
qed

theorem (in Blockchain) blockchain_safety :
  "\<forall> \<sigma>_set. \<sigma>_set \<subseteq> \<Sigma>t
  \<longrightarrow> finite \<sigma>_set
  \<longrightarrow> is_faults_lt_threshold (\<Union> \<sigma>_set)
  \<longrightarrow> (\<forall> \<sigma> \<sigma>' b1 b2. {\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2) \<and> block_membership b1 \<in> consensus_value_property_decisions \<sigma> 
      \<longrightarrow> block_membership b2 \<notin> consensus_value_property_decisions \<sigma>')"
  apply (rule, rule, rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma>_set \<sigma> \<sigma>' b1 b2
   assume "\<sigma>_set \<subseteq> \<Sigma>t" and "finite \<sigma>_set" and "is_faults_lt_threshold (\<Union>\<sigma>_set)" 
   and "{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2) \<and> block_membership b1 \<in> consensus_value_property_decisions \<sigma>" 
   and "block_membership b2 \<in> consensus_value_property_decisions \<sigma>'" 
   hence "\<not> consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>')"
      using negation_is_not_decided_by_other_validator \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>finite \<sigma>_set\<close> \<open>is_faults_lt_threshold (\<Union>\<sigma>_set)\<close> apply (simp add: consensus_value_property_decisions_def) 
      using \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2) \<and> block_membership b1 \<in> consensus_value_property_decisions \<sigma>\<close> by auto
   have "{b1, b2} \<subseteq> C \<and> \<sigma> \<in> \<Sigma> \<and> block_conflicting (b1, b2)"
     using \<Sigma>t_is_subset_of_\<Sigma> \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2) \<and> block_membership b1 \<in> consensus_value_property_decisions \<sigma>\<close> by auto
   hence "consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>')"
     using \<open>block_membership b2 \<in> consensus_value_property_decisions \<sigma>'\<close> conflicting_blocks_imps_conflicting_decision
     apply (simp add: consensus_value_property_decisions_def)
     by (metis \<open>\<sigma>_set \<subseteq> \<Sigma>t\<close> \<open>finite \<sigma>_set\<close> \<open>is_faults_lt_threshold (\<Union>\<sigma>_set)\<close> \<open>{\<sigma>, \<sigma>'} \<subseteq> \<sigma>_set \<and> {b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2) \<and> block_membership b1 \<in> consensus_value_property_decisions \<sigma>\<close> conflicting_blocks_imps_conflicting_decision consensus_value_property_decisions_def insert_subset mem_Collect_eq negation_is_not_decided_by_other_validator) 
   then show False
     using \<open>\<not> consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>')\<close> by blast
 qed

(* Two-party blockchain safety *)
theorem (in Blockchain) no_decision_on_conflicting_blocks :
  "\<forall> \<sigma>1 \<sigma>2. {\<sigma>1, \<sigma>2} \<subseteq> \<Sigma>t
  \<longrightarrow> is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)
  \<longrightarrow> (\<forall> b1 b2. {b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2) 
      \<longrightarrow> block_membership b1 \<in> consensus_value_property_decisions \<sigma>1 
      \<longrightarrow> block_membership b2 \<notin> consensus_value_property_decisions \<sigma>2)"
  apply (rule, rule, rule, rule, rule, rule, rule, rule, rule)
proof -
  fix \<sigma>1 \<sigma>2 b1 b2
  assume "{\<sigma>1, \<sigma>2} \<subseteq> \<Sigma>t" and "is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)" and "{b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2)" 
  and "block_membership b1 \<in> consensus_value_property_decisions \<sigma>1" 
  and "block_membership b2 \<in> consensus_value_property_decisions \<sigma>2" 
  hence "consensus_value_property_is_decided (block_membership b1, \<sigma>1)"
    by (simp add: consensus_value_property_decisions_def)
  hence "\<not> consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>2)"      
    using two_party_consensus_safety_for_consensus_value_property \<open>is_faults_lt_threshold (\<sigma>1 \<union> \<sigma>2)\<close> \<open>{\<sigma>1, \<sigma>2} \<subseteq> \<Sigma>t\<close> by blast
  have "block_membership b2 \<in> consensus_value_property_decisions \<sigma>2"
    using \<open>block_membership b2 \<in> consensus_value_property_decisions \<sigma>2\<close> 
    by (simp add: consensus_value_property_decisions_def)
  have "\<sigma>2 \<in> \<Sigma>t \<and> {b2, b1} \<subseteq> C \<and> block_conflicting (b2, b1)"
    using block_is_consensus_value \<open>{\<sigma>1, \<sigma>2} \<subseteq> \<Sigma>t\<close> \<open>{b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2)\<close> by (simp add: block_conflicting_def)
  hence "consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>2)"
    using  conflicting_blocks_imps_conflicting_decision \<open>block_membership b2 \<in> consensus_value_property_decisions \<sigma>2\<close> 
    using \<Sigma>t_is_subset_of_\<Sigma> consensus_value_property_decisions_def by auto      
  then show False
     using \<open>\<not> consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>2)\<close> by blast
 qed


(* Locale for proofs *)
locale Ghost = BlockchainParams + Protocol +
  assumes block_type : "\<forall> b. b \<in> C \<longleftrightarrow> prev b \<in> C"
  and ghost_is_estimator : "\<epsilon> = GHOST_estimator"
  and genesis_type : "genesis \<in> C"

lemma (in Ghost) children_type :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  children (b, \<sigma>) \<subseteq> C"
  apply (simp add: children_def)
  using Ghost_axioms Ghost_axioms_def Ghost_def by auto

lemma argmax_type :
  "S \<subseteq> A \<Longrightarrow> arg_max_on f S \<in> A" 
  apply (simp add: arg_max_on_def arg_max_def is_arg_max_def)
  oops

lemma (in Ghost) best_children_type :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  best_children (b, \<sigma>) \<subseteq> C"
  apply (simp add: best_children_def arg_max_on_def arg_max_def is_arg_max_def)
  using children_type 
  apply auto
  oops

lemma (in Ghost) GHSOT_type :
  "\<forall> \<sigma> b_set. \<sigma> \<in> \<Sigma> \<and> b_set \<subseteq> C \<longrightarrow>  GHOST(b_set, \<sigma>) \<subseteq> C"
  oops

lemma (in BlockchainParams) GHOST_is_valid_estimator : 
  "(\<forall> b. b \<in> C \<longleftrightarrow> prev b \<in> C) \<and> genesis \<in> C 
  \<Longrightarrow> is_valid_estimator GHOST_estimator"
  apply (simp add: is_valid_estimator_def BlockchainParams.GHOST_estimator_def)
  oops

lemma (in Ghost) block_membership_is_majority_driven :
  "\<forall> p \<in> P. is_majority_driven p"
  apply (simp add: is_majority_driven_def)
  (* by (metis DiffE Pow_iff is_valid_estimator_def \<epsilon>_type block_is_consensus_value subsetCE) *)
  oops

lemma (in Ghost) block_membership_is_max_driven :
  "\<forall> p \<in> P. is_max_driven p"
  apply (simp add: is_max_driven_def)
  (* FIXME: Timeout *)
  (* by (metis DiffE Nats_0 ghost_is_estimator) *)
  oops

end
