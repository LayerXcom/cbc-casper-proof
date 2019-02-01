theory CBCCasper

imports Main HOL.Real

begin

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


locale Params =
  fixes V :: "validator set"
  and W :: "validator \<Rightarrow> real"
  and t :: real
  and \<Sigma> :: "state set"
  and M :: "message set"

locale AbstractProtocol = Params +
  fixes C :: "consensus_value set"
  and \<epsilon> :: "message set \<Rightarrow> consensus_value set"
  assumes C_type: "card C > 1"
  and \<epsilon>_type: "\<And>s. s \<in> \<Sigma> \<Longrightarrow> \<epsilon> s \<in> Pow C - {\<emptyset>}"


(* \<Sigma>, M Construction
   NOTE: we cannot refer to the definitions from locale to its context *)
fun
  \<Sigma>_i :: "(validator set \<times> consensus_value set \<times> (message set \<Rightarrow> consensus_value set)) \<Rightarrow> nat \<Rightarrow> state set" and
  M_i :: "(validator set \<times> consensus_value set \<times> (message set \<Rightarrow> consensus_value set)) \<Rightarrow> nat \<Rightarrow> message set"
  where 
    "\<Sigma>_i (V,C,\<epsilon>) 0 = {\<emptyset>}"
  | "\<Sigma>_i (V,C,\<epsilon>) n = {\<sigma> \<in> Pow (M_i (V,C,\<epsilon>) (n - 1)). \<forall> m. m \<in> \<sigma> \<longrightarrow> justification m \<subseteq> \<sigma>}"
  | "M_i (V,C,\<epsilon>) n = {m. est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> (\<Sigma>_i (V,C,\<epsilon>) n) \<and> est m \<in> \<epsilon> (justification m)}" 

(* Locale for proofs *)
locale Protocol = AbstractProtocol +
  assumes V_type "V \<noteq> \<emptyset>"
  and W_type: "\<And>w. w \<in> range W \<Longrightarrow> w > 0"
  and t_type: "0 \<le> t" "t < Sum (W ` V)"

  assumes \<Sigma>_def: "\<Sigma> = (\<Union>i\<in>\<nat>. \<Sigma>_i (V,C,\<epsilon>) i)"
  and M_def: "M = (\<Union>i\<in>\<nat>. M_i (V,C,\<epsilon>) i)"
begin

lemma (in Protocol) message_in_state_is_valid :
  "\<forall> \<sigma> m. \<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma> \<longrightarrow>  m \<in> M"
  apply (rule, rule, rule)
proof -
  fix \<sigma> m
  assume "\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>"
  have
    "\<exists> n \<in> \<nat>. \<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n"
    using \<Sigma>_def \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>\<close> by auto
  moreover have
    "\<exists> n \<in> \<nat>. \<sigma> \<in> \<Sigma>_i (V, C, \<epsilon>) n
    \<longrightarrow> \<sigma> \<in> Pow (M_i (V, C, \<epsilon>) (n - 1))"
    by (metis One_nat_def \<Sigma>_i.simps(1) \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>\<close> diff_Suc_1 diff_add_inverse empty_iff insert_iff of_nat_1 of_nat_Suc of_nat_in_Nats)
  moreover have
    "\<exists> n \<in> \<nat>. \<sigma> \<in> Pow (M_i (V, C, \<epsilon>) (n - 1))  
    \<longrightarrow> (m \<in> \<sigma> \<longrightarrow> m \<in> M_i (V, C, \<epsilon>) (n - 1))"
    using calculation(2) by blast
  moreover have
    "\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)
    \<Longrightarrow> \<exists> n'\<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) n'"
  proof -
    assume "\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)"
    then obtain n :: nat where "n \<in> \<nat>" "m \<in> M_i (V, C, \<epsilon>) (n - 1)" by auto
    show ?thesis
      apply auto
      using \<open>\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)\<close> apply auto[1]
      using \<open>\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)\<close> apply auto[1]
      apply (metis (no_types, lifting) M_i.simps \<open>\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)\<close> id_apply mem_Collect_eq of_nat_eq_id of_nat_in_Nats)
      using \<open>\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1)\<close> by auto
  qed  
  moreover have
    "\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) n
    \<Longrightarrow> m \<in> M"
    using M_def by blast 
  ultimately show
    "m \<in> M"
    by (smt PowD \<Sigma>_i.elims \<open>\<sigma> \<in> \<Sigma> \<and> m \<in> \<sigma>\<close> empty_iff insert_iff mem_Collect_eq subsetCE)
qed

lemma (in Protocol) state_is_subset_of_M : "\<forall> \<sigma> \<in> \<Sigma>. \<sigma> \<subseteq> M"
  using message_in_state_is_valid by blast

lemma (in Protocol) state_difference_is_valid_message :
  "\<forall> \<sigma> \<sigma>'. \<sigma> \<in> \<Sigma> \<and> \<sigma>' \<in> \<Sigma>
  \<longrightarrow> is_future_state(\<sigma>', \<sigma>)
  \<longrightarrow> \<sigma>' - \<sigma> \<subseteq> M"
  using state_is_subset_of_M by blast

lemma (in Protocol) state_is_in_pow_M_i :
  "\<forall> \<sigma> \<in> \<Sigma>. (\<exists> n \<in> \<nat>. \<sigma> \<in> Pow (M_i (V, C, \<epsilon>) (n - 1)) \<and> (\<forall> m \<in> \<sigma>. justification m \<subseteq> \<sigma>))" 
  apply (simp add: \<Sigma>_def)
  by (smt M_i.simps One_nat_def PowD \<Sigma>_i.elims empty_iff insert_iff mem_Collect_eq subsetCE subsetI)

lemma (in Protocol) message_is_in_M_i :
  "\<forall> m \<in> M. (\<exists> n \<in> \<nat>. m \<in> M_i (V, C, \<epsilon>) (n - 1))"
  apply (simp add: M_def \<Sigma>_i.elims)
  by (metis Nats_1 Nats_add One_nat_def diff_Suc_1 plus_1_eq_Suc)

(* FIXME: \<Sigma> should be a strict subset of Pow M. #49 *)
lemma (in Protocol) \<Sigma>_type: "\<Sigma> \<subseteq> Pow M"
  by (simp add: state_is_subset_of_M subsetI)

(* FIXME: M should be a strict subset of C \<times> V \<times> \<Sigma>. #50 *)
lemma (in Protocol) M_type: "\<And>m. m \<in> M \<Longrightarrow> est m \<in> C \<and> sender m \<in> V \<and> justification m \<in> \<Sigma>"
  unfolding M_def \<Sigma>_def
  apply auto
  done

lemma estimates_are_non_empty: "\<And> \<sigma>. \<sigma> \<in> \<Sigma> \<Longrightarrow> \<epsilon> \<sigma> \<noteq> \<emptyset>"
  using \<epsilon>_type by auto
end

(* Definition 4.1: Observed validators *)
definition observed :: "state \<Rightarrow> validator set"
  where
    "observed \<sigma> = {sender m | m. m \<in> \<sigma>}"

lemma (in Protocol) oberved_type :
  "\<forall> \<sigma> \<in> \<Sigma>. observed \<sigma> \<subseteq> V"
  using Protocol.M_type Protocol_axioms observed_def state_is_subset_of_M by fastforce

(* Definition 2.8: Protocol state transitions \<rightarrow> *)
fun is_future_state :: "(state * state) \<Rightarrow> bool"
  where
    "is_future_state (\<sigma>1, \<sigma>2) = (\<sigma>1 \<supseteq> \<sigma>2)"

(* Definition 2.9 *)
fun equivocation :: "(message * message) \<Rightarrow> bool"
  where
    "equivocation (m1, m2) =
      (sender m1 = sender m2 \<and> m1 \<noteq> m2 \<and> m1 \<notin> justification m2 \<and> m2 \<notin> justification m1)"

(* Definition 2.10 *)
definition is_equivocating :: "state \<Rightarrow> validator \<Rightarrow> bool"
  where
    "is_equivocating \<sigma> v =  (\<exists> m1 \<in> \<sigma>. \<exists> m2 \<in> \<sigma>. equivocation (m1, m2) \<and> sender m1 = v)"

definition equivocating_validators :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators \<sigma> = {v \<in> observed \<sigma>. is_equivocating \<sigma> v}"

definition (in Params) equivocating_validators_paper :: "state \<Rightarrow> validator set"
  where
    "equivocating_validators_paper \<sigma> = {v \<in> V. is_equivocating \<sigma> v}"

lemma (in Protocol) equivocating_validators_is_equivalent_to_paper :
  "\<forall> \<sigma> \<in> \<Sigma>. equivocating_validators \<sigma> = equivocating_validators_paper \<sigma>"
  by (meson Protocol.axioms(2) Protocol_axioms Protocol_axioms_def)


(* Definition 2.11 *)
definition (in Params) equivocation_fault_weight :: "state \<Rightarrow> real"
  where
    "equivocation_fault_weight \<sigma> = sum W (equivocating_validators \<sigma>)"

(* Definition 2.12 *)
definition (in Params) is_faults_lt_threshold :: "state \<Rightarrow> bool"
  where 
    "is_faults_lt_threshold \<sigma> = (equivocation_fault_weight \<sigma> < t)"

definition (in Params) \<Sigma>t :: "state set"
  where
    "\<Sigma>t = {\<sigma> \<in> \<Sigma>. is_faults_lt_threshold \<sigma>}" 

lemma (in Protocol) \<Sigma>t_is_subset_of_\<Sigma> : "\<Sigma>t \<subseteq> \<Sigma>"
  using \<Sigma>t_def by auto

(* Definition 3.2 *)
type_synonym state_property = "state \<Rightarrow> bool"

(* Definition 3.7 *)
type_synonym consensus_value_property = "consensus_value \<Rightarrow> bool"

end
