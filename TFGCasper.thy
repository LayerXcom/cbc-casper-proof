theory TFGCasper

imports Main HOL.Real CBCCasper ConsensusSafety ExampleProtocols

begin

(* Section 4.4: Casper the Friendly GHOST *)
(* Definition 4.23: Blocks *)
type_synonym block = consensus_value

type_synonym genesis = block

type_synonym next_block_generator = "block \<Rightarrow> block set"

datatype ghost_params = GHOST_params "genesis * next_block_generator"

fun g :: "ghost_params \<Rightarrow> block"
  where
    "g (GHOST_params (gblk, _)) = gblk"

fun blk_gen :: "ghost_params \<Rightarrow> next_block_generator"
  where
    "blk_gen (GHOST_params (_, bgen)) = bgen"

fun B_i :: "ghost_params \<Rightarrow> nat \<Rightarrow> block set"
  where
    "B_i gparams 0 = {g gparams}"
  | "B_i gparams n = \<Union> {blk_gen gparams b | b. b \<in> B_i gparams (n - 1)}"

fun B :: "ghost_params \<Rightarrow> block set"
  where
    "B block_params = \<Union> (B_i block_params `\<nat>)"

(* Definition 4.24: Previous block resolver *)
fun prev :: "ghost_params \<Rightarrow> block \<Rightarrow> block set"
  where
    "prev gparams b = (if b = g gparams then {g gparams} else {b'. b' \<in> B gparams \<and> b \<in> blk_gen gparams b'})"

(* Definition 4.25: n'th generation ansectr block *)
fun n_cestor :: "ghost_params \<Rightarrow> block \<Rightarrow> nat \<Rightarrow> block set"
  where
    "n_cestor gparams b 0 = {b}"
  | "n_cestor gparams b n = {b. \<forall> prevblk. prevblk \<in> (prev gparams b) \<and> (b \<in> n_cestor gparams prevblk (n-1))}"

(* Definition 4.26: Blockchain membership *)
fun blockchain_membership :: "ghost_params \<Rightarrow> block * block \<Rightarrow> bool"
  where
    "blockchain_membership gparams (b1, b2) = (\<exists> n. n \<in> \<nat> \<and> (b1 \<in> n_cestor gparams b2 n))"

(* Definition 4.27: Score of a block *)
fun (in Protocol) score :: "ghost_params \<Rightarrow> block * state \<Rightarrow> real"
  where
    "score gparams (b, \<sigma>) = sum W ({v. \<forall> v. \<exists> b'. v \<in> V \<and> b' \<in> (latest_estimates_from_non_equivocating_validators \<sigma> v) \<and> (blockchain_membership gparams (b, b'))})"

(* Definition 4.28: Children *)
fun single_est_set :: "message \<Rightarrow> block set"
  where
    "single_est_set m = {b . b = est m}"

fun children :: "ghost_params \<Rightarrow> block * state \<Rightarrow> block set"
  where
    "children gparams (b, \<sigma>) = {b'. \<forall> b'. \<forall> m. m \<in> \<sigma> \<and> b' \<in> \<Union> (single_est_set ` \<sigma>) \<and> (b \<in> prev gparams b')}"
    (* same meaning? *)
    (* "children gparams (b, \<sigma>) = {b'. \<forall> b'. (b' \<in> est ` \<sigma>) \<and> (b \<in> prev gparams b')}" *)

(* Definition 4.29: Best Children *)
fun (in Protocol) best_children :: "ghost_params \<Rightarrow> block * state \<Rightarrow>  block set"
  where
    "best_children gparams (b, \<sigma>) = {b'. \<forall> b'.
    (b' \<in> children gparams (b, \<sigma>)) \<and> 
    \<not> (\<exists> b''. (b'' \<in> children gparams (b, \<sigma>)) \<and> (score gparams (b'', \<sigma>)) > (score gparams (b', \<sigma>)))}"

(* Definition 4.30: GHOST *)
function (in Protocol) GHOST :: "ghost_params \<Rightarrow> (block set) * state => block set"
  where
    "GHOST gparams (b_set, \<sigma>) =  
    (\<Union> {s. \<forall> b. s = GHOST gparams ((best_children gparams (b, \<sigma>)), \<sigma>) \<and> b \<in> b_set \<and> (children gparams (b, \<sigma>) \<noteq> \<emptyset>)})
    \<union>
    (\<Union> {s. \<forall> b. s = {b} \<and> b \<in> b_set \<and> (children gparams (b, \<sigma>) = \<emptyset>)})"
  by auto

(* Definition 4.31: Casper the Friendly Ghost *)
fun (in Protocol) estimator :: "ghost_params \<Rightarrow> state \<Rightarrow> block set"
  where
    "estimator gparams \<sigma> = GHOST gparams ({g gparams}, \<sigma>)"

(* Definition 4.32: Example non-trivial properties of consensus values *)
fun P :: "ghost_params \<Rightarrow> consensus_value_property set \<Rightarrow> block set \<Rightarrow> consensus_value_property set"
  where
    "P gparams p_set b_set = {p. \<exists>!b. \<forall>b'. b \<in> b_set \<and> b' \<in> b_set \<and> (blockchain_membership gparams (b, b') \<longrightarrow> p b' = True) \<and> \<not> (blockchain_membership gparams (b, b') \<longrightarrow> p b' = False) }"

end