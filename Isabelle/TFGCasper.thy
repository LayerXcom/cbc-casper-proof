theory TFGCasper

imports Main HOL.Real CBCCasper LatestMessage CliqueOracle ConsensusSafety

begin

(* ###################################################### *)
(* Blockchain consensus protocol *)
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

lemma (in BlockchainParams) prev_membership :
  "prev b \<downharpoonright> b"
  apply (simp add: blockchain_membership_def)
  by (metis BlockchainParams.n_cestor.simps(1) BlockchainParams.n_cestor.simps(2) Nats_1 One_nat_def diff_Suc_1) 

definition (in BlockchainParams) block_conflicting :: "(consensus_value * consensus_value) \<Rightarrow> bool"
  where
    "block_conflicting = (\<lambda>(b1, b2). \<not> (b1 \<downharpoonright> b2 \<or> b2 \<downharpoonright> b1))"

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
  "b1 \<downharpoonright> b2 \<and> b2 \<downharpoonright> b3 \<Longrightarrow> b1 \<downharpoonright> b3"
  apply (simp add: blockchain_membership_def)
  using n_cestor_transitive
  by (metis id_apply of_nat_eq_id of_nat_in_Nats subsetI)

lemma (in BlockchainParams) irreflexivity_of_blockchain_membership :
  "b \<downharpoonright> b"
  apply (simp add: blockchain_membership_def)
  using Nats_0 by fastforce

(* Block membership property *)
(* This is Definition 4.32: Example non-trivial properties of consensus values *)
definition (in BlockchainParams) block_membership :: "consensus_value \<Rightarrow> consensus_value_property"
  where
    "block_membership b = (\<lambda>b'. b \<downharpoonright> b')"

lemma (in BlockchainParams) also_agreeing_on_ancestors :
  "b' \<downharpoonright> b \<Longrightarrow> agreeing (block_membership b, \<sigma>, v) \<Longrightarrow> agreeing (block_membership b', \<sigma>, v)"
  apply (simp add: agreeing_def block_membership_def)
  using BlockchainParams.transitivity_of_blockchain_membership by blast

(* Definition 4.28: Children *)
(* NOTE: Modified from the paper to include non-observed blocks so that (block_membership b) becomes max-driven for any b \<in> C *)
definition (in BlockchainParams) children :: "consensus_value * state \<Rightarrow> consensus_value set"
  where
    "children = (\<lambda>(b, \<sigma>). {b' \<in> est `\<sigma>. b = prev b'})"

lemma (in BlockchainParams) observed_block_is_children_of_prev_block :
  "\<forall> b \<in> est `\<sigma>. b \<in> children (prev b, \<sigma>)"
  by (simp add: children_def)  

lemma (in BlockchainParams) children_membership :
  "\<forall> b \<in> children (b', \<sigma>).  b' \<downharpoonright> b"
  apply (simp add: children_def) 
  by (metis BlockchainParams.blockchain_membership_def BlockchainParams.n_cestor.simps(2) diff_Suc_1 id_apply n_cestor.simps(1) of_nat_eq_id of_nat_in_Nats)

(* ###################################################### *)
(* Blockchain safety *)
(* ###################################################### *)

(* Locale for proofs *)
locale Blockchain = BlockchainParams + Protocol +
  (* FIXME: More general blockchain detatype #97 *)
  assumes blockchain_type : "\<forall> b b' b''. {b, b', b''} \<subseteq> C \<longrightarrow> b' \<downharpoonright> b \<and> b'' \<downharpoonright> b \<longrightarrow> (b' \<downharpoonright> b'' \<or> b'' \<downharpoonright> b')"
  and children_conflicting : "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b1 b2. {b, b1, b2} \<subseteq> C \<and> {b1, b2} \<subseteq> children (b, \<sigma>) \<longrightarrow> block_conflicting (b1, b2)"
  and prev_type : "\<forall> b. b \<in> C \<longleftrightarrow> prev b \<in> C"
  and genesis_type : "genesis \<in> C" "\<forall> b \<in> C. genesis \<downharpoonright> b" "prev genesis = genesis"

lemma (in Blockchain) children_type :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  children (b, \<sigma>) \<subseteq> C"
  apply (simp add: children_def)
  using prev_type by auto

lemma (in Blockchain) children_finite :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  finite (children (b, \<sigma>))"
  apply (simp add: children_def)
  using state_is_finite
  by simp
   
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
      using \<Sigma>t_is_subset_of_\<Sigma> \<open>b1 \<in> C \<and> b2 \<in> C \<and> \<sigma> \<in> \<Sigma>\<close> estimates_are_subset_of_C futures_def by blast
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
    using \<open>{\<sigma>1, \<sigma>2} \<subseteq> \<Sigma>t\<close> \<open>{b1, b2} \<subseteq> C \<and> block_conflicting (b1, b2)\<close> by (simp add: block_conflicting_def)
  hence "consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>2)"
    using  conflicting_blocks_imps_conflicting_decision \<open>block_membership b2 \<in> consensus_value_property_decisions \<sigma>2\<close> 
    using \<Sigma>t_is_subset_of_\<Sigma> consensus_value_property_decisions_def by auto      
  then show False
     using \<open>\<not> consensus_value_property_is_decided (consensus_value_property_not (block_membership b1), \<sigma>2)\<close> by blast
 qed

(* ###################################################### *)
(* Casper TFG *)
(* ###################################################### *)

(* Definition 4.27: Score of a block *)
definition (in BlockchainParams) score :: "state \<Rightarrow> consensus_value \<Rightarrow> real"
  where
    "score \<sigma> b = weight_measure (agreeing_validators (block_membership b, \<sigma>))"  

(* A lemma to show the equivalence of the above definition of score and the one in the paper *)
lemma (in Blockchain) unfolding_agreeing_on_block_membership :
  "\<forall> \<sigma> \<in> \<Sigma>. agreeing_validators (block_membership b, \<sigma>) =  {v \<in> V. \<exists> b' \<in> L_H_E \<sigma> v. b \<downharpoonright> b'}"
proof -
  have "\<forall> v \<sigma>. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  v \<notin> equivocating_validators \<sigma> 
        \<longrightarrow> (v \<in> observed \<sigma> \<and> (\<forall> x \<in> L_M \<sigma> v. b \<downharpoonright> est x)) = (v \<in> observed \<sigma> \<and> (\<exists> x \<in>L_M \<sigma> v. b \<downharpoonright> est x))"
    using observed_non_equivocating_validators_have_one_latest_message
    unfolding observed_non_equivocating_validators_def is_singleton_def
    by (metis Diff_iff empty_iff insert_iff)
  moreover have "\<forall> v \<sigma>. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  v \<notin> equivocating_validators \<sigma> 
        \<longrightarrow> (v \<in> V \<and> (\<exists> x \<in>L_M \<sigma> v. b \<downharpoonright> est x)) = (v \<in> observed \<sigma> \<and> (\<exists> x \<in>L_M \<sigma> v. b \<downharpoonright> est x))"
    apply (simp add: observed_def L_M_def from_sender_def)
    by auto
  ultimately have "\<forall> v \<sigma>. v \<in> V \<and> \<sigma> \<in> \<Sigma> \<longrightarrow>  v \<notin> equivocating_validators \<sigma> 
        \<longrightarrow> (v \<in> V \<and> (\<exists> x \<in>L_M \<sigma> v. b \<downharpoonright> est x)) = (v \<in> observed \<sigma> \<and> (\<forall> x \<in> L_M \<sigma> v. b \<downharpoonright> est x))"
    by blast
  then have "\<forall> v \<sigma>. v \<in> V \<and> \<sigma> \<in> \<Sigma>
        \<longrightarrow> (v \<notin> equivocating_validators \<sigma> \<longrightarrow> v \<in> V \<and> (\<exists> x \<in>L_M \<sigma> v. b \<downharpoonright> est x)) = (v \<notin> equivocating_validators \<sigma> \<longrightarrow> v \<in> observed \<sigma> \<and> (\<forall> x \<in> L_M \<sigma> v. b \<downharpoonright> est x))"
    by blast
  show ?thesis
    apply (simp add: agreeing_validators_def agreeing_def observed_non_equivocating_validators_def L_H_E_def L_H_M_def block_membership_def)
    using \<open>\<forall> v \<sigma>. v \<in> V \<and> \<sigma> \<in> \<Sigma>
        \<longrightarrow> (v \<notin> equivocating_validators \<sigma> \<longrightarrow> v \<in> V \<and> (\<exists> x \<in>L_M \<sigma> v. b \<downharpoonright> est x)) = (v \<notin> equivocating_validators \<sigma> \<longrightarrow> v \<in> observed \<sigma> \<and> (\<forall> x \<in> L_M \<sigma> v. b \<downharpoonright> est x))\<close>
    observed_type_for_state
    by blast
qed

definition (in BlockchainParams) score_magnitude :: "state \<Rightarrow> consensus_value rel"
  where 
    "score_magnitude \<sigma> = {(b1, b2). {b1, b2} \<subseteq> C \<and> score \<sigma> b1 \<le> score \<sigma> b2}" 

lemma (in Blockchain) transitivity_of_score_magnitude :
  "\<forall> \<sigma> \<in> \<Sigma>. trans (score_magnitude \<sigma>)"
  by (simp add: trans_def score_magnitude_def)
  
lemma (in Blockchain) reflexivity_of_score_magnitude :
  "\<forall> \<sigma> \<in> \<Sigma>. refl_on C (score_magnitude \<sigma>)"
  apply (simp add: refl_on_def score_magnitude_def)
  by auto
  
lemma (in Blockchain) score_magnitude_is_preorder :
  "\<forall> \<sigma> \<in> \<Sigma>. preorder_on C (score_magnitude \<sigma>)"
  unfolding preorder_on_def 
  using reflexivity_of_score_magnitude transitivity_of_score_magnitude by simp

lemma (in Blockchain) totality_of_score_magnitude :
  "\<forall> \<sigma> \<in> \<Sigma>. Relation.total_on C (score_magnitude \<sigma>)"
  apply (simp add: Relation.total_on_def score_magnitude_def)
  by auto

(* FIXME: Reuse score_magnitude, Subset of preordered & connex set is preordered & connex? #109 *)
definition (in BlockchainParams) score_magnitude_children :: "state \<Rightarrow> consensus_value \<Rightarrow> consensus_value rel"
  where 
    "score_magnitude_children \<sigma> b = {(b1, b2). {b1, b2} \<subseteq> children (b, \<sigma>) \<and> score \<sigma> b1 \<le> score \<sigma> b2}" 

lemma (in Blockchain) transitivity_of_score_magnitude_children :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. trans (score_magnitude_children \<sigma> b)"
  by (simp add: trans_def score_magnitude_children_def)
  
lemma (in Blockchain) reflexivity_of_score_magnitude_children :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. refl_on (children (b, \<sigma>)) (score_magnitude_children \<sigma> b)"
  apply (simp add: refl_on_def score_magnitude_children_def)
  by blast 

lemma (in Blockchain) score_magnitude_children_is_preorder :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. preorder_on (children (b, \<sigma>)) (score_magnitude_children \<sigma> b)"
  unfolding preorder_on_def 
  using reflexivity_of_score_magnitude_children transitivity_of_score_magnitude_children by simp

lemma (in Blockchain) totality_of_score_magnitude_children :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. Relation.total_on (children (b, \<sigma>)) (score_magnitude_children \<sigma> b)"
  apply (simp add: Relation.total_on_def score_magnitude_children_def)
  by auto

(* Definition 4.29: Best Children *)
definition (in BlockchainParams) best_children :: "consensus_value * state \<Rightarrow> consensus_value set"
  where
    "best_children = (\<lambda> (b, \<sigma>). {b' \<in> C. is_arg_max (score \<sigma>) (\<lambda>b'. b' \<in> children (b, \<sigma>)) b'})"

lemma (in Blockchain) best_children_type :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow> best_children (b, \<sigma>) \<subseteq> C"
  by (simp add: is_arg_max_def best_children_def)

lemma (in Blockchain) best_children_finite :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow> finite (best_children (b, \<sigma>))"
  apply (simp add: best_children_def is_arg_max_def)
  using children_finite
  by auto
 
lemma (in Blockchain) best_children_existence :
  "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow> children (b, \<sigma>) \<noteq> \<emptyset> \<longrightarrow> best_children (b, \<sigma>) \<in> Pow C - {\<emptyset>}"    
proof -
  have "\<forall> b \<sigma>. b \<in> C \<and> \<sigma> \<in> \<Sigma> \<longrightarrow> children (b, \<sigma>) \<noteq> \<emptyset> 
    \<longrightarrow> (\<exists> b'. maximum_on_non_strict (children (b, \<sigma>)) (score_magnitude_children \<sigma> b) b')"  
    using totality_of_score_magnitude_children score_magnitude_children_is_preorder
        children_finite children_type connex_preorder_on_finite_non_empty_set_has_maximum
    by blast
  then show ?thesis
    apply (simp add: score_magnitude_children_def best_children_def is_arg_max_def)
    apply (simp add: maximum_on_non_strict_def upper_bound_on_non_strict_def)
    apply auto
    by (smt children_type ex_in_conv subsetCE)
qed

(* Best children property *)
definition (in BlockchainParams) best_child :: "consensus_value \<Rightarrow> state_property"
  where
    "best_child b = (\<lambda>\<sigma>. b \<in> best_children (prev b, \<sigma>))"

(* Definition 4.30: LMD GHOST *)
(* NOTE: well-sortedness error occurs in code generation *)
function (in BlockchainParams) GHOST :: "(consensus_value set * state) \<Rightarrow> consensus_value set"
  where
    "GHOST (b_set, \<sigma>) =
      (\<Union> b \<in> {b \<in> b_set. children (b, \<sigma>) \<noteq> \<emptyset>}. GHOST (best_children (b, \<sigma>), \<sigma>))
         \<union> {b \<in> b_set. children (b, \<sigma>) = \<emptyset>}"
  by auto

definition (in BlockchainParams) GHOST_heads_or_children :: "state \<Rightarrow> consensus_value set"
  where
    "GHOST_heads_or_children \<sigma> = GHOST ({genesis}, \<sigma>) \<union> (\<Union> b \<in> GHOST ({genesis}, \<sigma>). children (b, \<sigma>))"

lemma (in Blockchain) GHOST_type :
  "\<forall> \<sigma> b_set. \<sigma> \<in> \<Sigma> \<and> b_set \<subseteq> C \<longrightarrow> GHOST (b_set, \<sigma>) \<subseteq> C"
proof - 
  (* By calculating the head of GHOST, it eventually reaches blocks with no child because the set of descendant blocks is finite. *)
  have "\<forall> \<sigma> b_set. \<sigma> \<in> \<Sigma> \<and> b_set \<subseteq> C \<longrightarrow> (\<exists> b_set'. b_set' \<subseteq> C \<and> GHOST (b_set, \<sigma>) = {b \<in> b_set'. children (b, \<sigma>) = \<emptyset>})"    
    sorry
  then show ?thesis
    by blast
qed    


lemma (in Blockchain) GHOST_is_valid_estimator :
  "is_valid_estimator GHOST_heads_or_children"
  unfolding is_valid_estimator_def
  apply (simp add:  BlockchainParams.GHOST_heads_or_children_def)
  apply auto
  using GHOST_type genesis_type(1) apply blast
  using GHOST_type children_type genesis_type(1) apply blast
  using best_children_existence  
  oops

(* Locale for proofs *)
(* Definition 4.31: Casper the Friendly GHOST *)
locale TFG = Blockchain + 
  assumes ghost_estimator : "\<epsilon> = GHOST_heads_or_children"

lemma (in TFG) block_membership_is_majority_driven :
  "\<forall> b \<in> C. majority_driven (block_membership b)"
  apply (simp add: majority_driven_def)
  oops

lemma (in Blockchain) agreeing_validators_on_sistor_blocks_are_disagreeing :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b1 b2. {b, b1, b2} \<subseteq> C \<and> {b1, b2} \<subseteq> children (b, \<sigma>) 
   \<longrightarrow>  agreeing_validators (block_membership b1, \<sigma>) \<subseteq> disagreeing_validators (block_membership b2, \<sigma>)"
proof - 
  have "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b1 b2. {b, b1, b2} \<subseteq> C \<and> {b1, b2} \<subseteq> children (b, \<sigma>) 
   \<longrightarrow>  (\<forall> v \<in> agreeing_validators (block_membership b1, \<sigma>). \<forall> c \<in>L_H_E \<sigma> v. block_membership b1 c)"
    by (simp add: agreeing_validators_def agreeing_def)
  hence "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b1 b2. {b, b1, b2} \<subseteq> C \<and> {b1, b2} \<subseteq> children (b, \<sigma>)
   \<longrightarrow>  (\<forall> v \<in> agreeing_validators (block_membership b1, \<sigma>). \<exists> c \<in>L_H_E \<sigma> v. \<not> block_membership b2 c)"
    using children_conflicting
    apply (simp add:  block_membership_def block_conflicting_def)
    using irreflexivity_of_blockchain_membership by fast        
  then show ?thesis
    using disagreeing_validators_include_not_agreeing_validators
    by (metis (no_types, lifting) \<open>\<forall>\<sigma>\<in>\<Sigma>. \<forall>b b1 b2. {b, b1, b2} \<subseteq> C \<and> {b1, b2} \<subseteq> children (b, \<sigma>) \<longrightarrow> (\<forall>v\<in>agreeing_validators (block_membership b1, \<sigma>). \<forall>c\<in>L_H_E \<sigma> v. block_membership b1 c)\<close> insert_subset subsetI)    
qed    

lemma (in Blockchain) agreeing_validators_on_sistor_blocks_are_not_more_than_disagreeing :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b1 b2. {b, b1, b2} \<subseteq> C \<and> {b1, b2} \<subseteq> children (b, \<sigma>) 
   \<longrightarrow>  weight_measure (agreeing_validators (block_membership b1, \<sigma>)) \<le> weight_measure (disagreeing_validators (block_membership b2, \<sigma>))"
  using agreeing_validators_on_sistor_blocks_are_disagreeing
        agreeing_validators_on_sistor_blocks_are_disagreeing weight_measure_subset_gte
        agreeing_validators_type disagreeing_validators_type
  by auto

lemma (in Blockchain) no_child_and_best_child_at_all_earlier_height_imps_GHOST_heads :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. children (b, \<sigma>) = \<emptyset> \<and>
    (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>))
    \<longrightarrow> b \<in> GHOST ({genesis}, \<sigma>)"
  apply auto 
  oops

lemma (in Blockchain) best_child_at_all_earlier_height_imps_GHOST_heads_or_decendant :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. 
    (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>))
    \<longrightarrow> (\<forall> b'' \<in> GHOST ({genesis}, \<sigma>). b \<downharpoonright> b'')"
proof -
  have "\<And> n. \<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> C. genesis = n_cestor (b, n) \<and>
    (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>))
    \<longrightarrow> (\<forall> b'' \<in> GHOST ({genesis}, \<sigma>). b \<downharpoonright> b'')"
  proof -
    fix n
    show "\<forall>\<sigma>\<in>\<Sigma>. \<forall>b\<in>C. genesis = n_cestor (b, n) \<and>
                      (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>)) \<longrightarrow>
                      (\<forall>b''\<in>GHOST ({genesis}, \<sigma>). b \<downharpoonright> b'')"
      apply (induction n) 
      using genesis_type GHOST_type
      apply (metis contra_subsetD empty_subsetI insert_subset n_cestor.simps(1))
    proof -
      fix n
      assume "\<forall>\<sigma>\<in>\<Sigma>. \<forall>b\<in>C. genesis = n_cestor (b, n) \<and>
                      (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>)) \<longrightarrow>
                      (\<forall>b''\<in>GHOST ({genesis}, \<sigma>). b \<downharpoonright> b'')" 
      show "\<forall>\<sigma>\<in>\<Sigma>. \<forall>b\<in>C. genesis = n_cestor (b, Suc n) \<and>
                      (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>)) \<longrightarrow>
                      (\<forall>b''\<in>GHOST ({genesis}, \<sigma>). b \<downharpoonright> b'')"
        apply (rule, rule, rule, rule)
      proof -
        fix \<sigma> b b''
        assume "\<sigma> \<in> \<Sigma>"
        and "b \<in> C"
        and "genesis = n_cestor (b, Suc n) \<and> (\<forall>b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>))"
        and "b'' \<in> GHOST ({genesis}, \<sigma>)"
        then have "genesis = n_cestor (prev b, n) \<and> (\<forall> b' \<in> C. b' \<downharpoonright> prev b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>))"
          by (metis BlockchainParams.blockchain_membership_def BlockchainParams.n_cestor.simps(2) diff_Suc_1 id_apply of_nat_eq_id of_nat_in_Nats)
        then have "prev b \<downharpoonright> b''"
          using \<open>\<forall>\<sigma>\<in>\<Sigma>. \<forall> b \<in> C. genesis = n_cestor (b, n) \<and>
                        (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>)) \<longrightarrow>
                        (\<forall>b''\<in>GHOST ({genesis}, \<sigma>). b \<downharpoonright> b'')\<close>
          using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>b \<in> C\<close> prev_type \<open>b'' \<in> GHOST ({genesis}, \<sigma>)\<close> by auto 
        have "b \<in> best_children (prev b, \<sigma>)"
          using \<open>genesis = n_cestor (b, Suc n) \<and> (\<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> best_children (prev b', \<sigma>))\<close>
          using \<open>b \<in> C\<close> irreflexivity_of_blockchain_membership by blast
        then show "b \<downharpoonright> b''"   
          using \<open>prev b \<downharpoonright> b''\<close> \<open>b'' \<in> GHOST ({genesis}, \<sigma>)\<close>          
          sorry
      qed
    qed
  qed
  then show ?thesis
    using blockchain_membership_def genesis_type(2) by auto
qed    

lemma (in TFG) ancestor_of_observed_block_is_observed :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> est `\<sigma>. \<forall> b' \<in> C. b' \<downharpoonright> b \<longrightarrow> b' \<in> est `\<sigma>"
  sorry

lemma (in TFG) block_membership_is_max_driven :
  "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b \<in> est `\<sigma>. max_driven_for_future (block_membership b) \<sigma>"
  apply (simp add: max_driven_for_future_def)
proof -
  have "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b'. {b, b'} \<subseteq> C \<and> b' \<downharpoonright> b
        \<longrightarrow> agreeing_validators (block_membership b, \<sigma>) \<subseteq> agreeing_validators (block_membership b', \<sigma>)"
    unfolding agreeing_validators_def
    using also_agreeing_on_ancestors by blast
  hence "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b'. {b, b'} \<subseteq> C \<and> b' \<downharpoonright> b 
        \<longrightarrow> weight_measure (agreeing_validators (block_membership b', \<sigma>)) \<ge> weight_measure (agreeing_validators (block_membership b, \<sigma>))"
    using weight_measure_subset_gte agreeing_validators_finite agreeing_validators_type by simp
  hence "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b'. {b, b'} \<subseteq> C \<and> b' \<downharpoonright> b 
        \<longrightarrow> weight_measure V - weight_measure (disagreeing_validators (block_membership b', \<sigma>)) - equivocation_fault_weight \<sigma> 
              \<ge> weight_measure V - weight_measure (disagreeing_validators (block_membership b, \<sigma>)) - equivocation_fault_weight \<sigma>"
    using agreeing_validators_weight_combined by simp
  hence "\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b'. {b, b'} \<subseteq> C \<and> b' \<downharpoonright> b
        \<longrightarrow> weight_measure (disagreeing_validators (block_membership b, \<sigma>)) 
              \<ge> weight_measure (disagreeing_validators (block_membership b', \<sigma>))"
    by simp
  show "\<forall> \<sigma> \<in> \<Sigma>. \<forall> m \<in> \<sigma>. \<forall> \<sigma>' \<in> \<Sigma>. \<sigma> \<subseteq> \<sigma>' \<longrightarrow> weight_measure (disagreeing_validators (block_membership (est m), \<sigma>')) < weight_measure (agreeing_validators (block_membership (est m), \<sigma>')) 
            \<longrightarrow> (\<forall> c \<in> \<epsilon> \<sigma>'. block_membership (est m) c)"
    apply (rule, rule, rule, rule, rule, rule)
  proof - 
    fix \<sigma> m \<sigma>' c
    assume "\<sigma> \<in> \<Sigma>"
    and "m \<in> \<sigma>"
    and "\<sigma>' \<in> \<Sigma>"
    and "\<sigma> \<subseteq> \<sigma>'"
    and "weight_measure (disagreeing_validators (block_membership (est m), \<sigma>')) < weight_measure (agreeing_validators (block_membership (est m), \<sigma>'))"
    and "c \<in> \<epsilon> \<sigma>'"
    hence "est m \<in> C"
      using M_type message_in_state_is_valid by blast
    hence "\<forall> b' \<in> C. b' \<downharpoonright> est m \<longrightarrow> weight_measure (agreeing_validators (block_membership b', \<sigma>')) > weight_measure (disagreeing_validators (block_membership (est m), \<sigma>'))"
      using \<open>\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b'. {b, b'} \<subseteq> C \<and> b' \<downharpoonright> b 
        \<longrightarrow> weight_measure (agreeing_validators (block_membership b', \<sigma>)) \<ge> weight_measure (agreeing_validators (block_membership b, \<sigma>))\<close>
          \<open>weight_measure (disagreeing_validators (block_membership (est m), \<sigma>')) < weight_measure (agreeing_validators (block_membership (est m), \<sigma>'))\<close>
          \<open>\<sigma>' \<in> \<Sigma>\<close> by fastforce      
    hence "\<forall> b' \<in> C. b' \<downharpoonright> est m \<longrightarrow> weight_measure (agreeing_validators (block_membership b', \<sigma>')) > weight_measure (disagreeing_validators (block_membership b', \<sigma>'))"
      using \<open>\<forall> \<sigma> \<in> \<Sigma>. \<forall> b b'. {b, b'} \<subseteq> C \<and> b' \<downharpoonright> b
        \<longrightarrow> weight_measure (disagreeing_validators (block_membership b, \<sigma>)) \<ge> weight_measure (disagreeing_validators (block_membership b', \<sigma>))\<close>
          \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>est m \<in> C\<close> by force
    (* Here we prove best_children property is max driven *)
    have "\<forall> b' \<in> C. b' \<downharpoonright> est m \<longrightarrow> b' \<in> best_children (prev b', \<sigma>')"
      apply (simp add: best_children_def is_arg_max_def score_def)
      apply (auto) 
      using ancestor_of_observed_block_is_observed
      apply (meson \<open>\<sigma> \<subseteq> \<sigma>'\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>m \<in> \<sigma>\<close> contra_subsetD image_eqI observed_block_is_children_of_prev_block) 
      using M_type Params.message_in_state_is_valid \<open>\<sigma> \<in> \<Sigma>\<close>
      using agreeing_validators_on_sistor_blocks_are_not_more_than_disagreeing 
            prev_type 
            \<open>\<forall> b' \<in> C. b' \<downharpoonright> est m \<longrightarrow> weight_measure (agreeing_validators (block_membership b', \<sigma>')) > weight_measure (disagreeing_validators (block_membership b', \<sigma>'))\<close>
      by (smt \<open>\<sigma>' \<in> \<Sigma>\<close> agreeing_validators_weight_combined children_type contra_subsetD empty_subsetI insert_absorb2 insert_subset)      
    have "c \<in> GHOST ({genesis}, \<sigma>') \<union> (\<Union> b \<in> GHOST ({genesis}, \<sigma>'). children (b, \<sigma>'))" 
      using ghost_estimator \<open>c \<in> \<epsilon> \<sigma>'\<close>
      unfolding GHOST_heads_or_children_def
      by blast
    have "\<forall> b'' \<in> GHOST ({genesis}, \<sigma>'). est m \<downharpoonright> b''"
      using best_child_at_all_earlier_height_imps_GHOST_heads_or_decendant \<open>\<forall> b' \<in> C. b' \<downharpoonright> est m \<longrightarrow> b' \<in> best_children (prev b', \<sigma>')\<close>
            \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>' \<in> \<Sigma>\<close> \<open>est m \<in> C\<close> by blast 
   then show "block_membership (est m) c"
     unfolding block_membership_def
     using \<open>c \<in> GHOST ({genesis}, \<sigma>') \<union> (\<Union> b \<in> GHOST ({genesis}, \<sigma>'). children (b, \<sigma>'))\<close>  
           transitivity_of_blockchain_membership children_membership
     by blast
 qed
qed

end
