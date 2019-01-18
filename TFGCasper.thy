theory TFGCasper

imports Main HOL.Real CBCCasper ExampleProtocols

begin

(* Section 4.4: Casper the Friendly GHOST *)

(* Definition 4.23: Blocks *)
datatype block_value = Block_value int
datatype block_data = Block_data
type_synonym block = "block_value + block_value * block_data"
datatype block_params = 
  Block_params "validator set * weight * threshold * block set * estimator_param"

fun blk :: "block_params \<Rightarrow> block set"
  where
    "blk(Block_params (_, _, _, b, _)) = b"

(* TODO *)
fun B_i :: "block_params \<Rightarrow> nat \<Rightarrow> block set"
  where
    "B_i block_params i =  blk block_params"

fun B :: "block_params \<Rightarrow> block set"
  where
    "B block_params = \<Union> (B_i block_params `\<nat>)"

(* Definition 4.24: Previous block resolver *)
fun prev :: "block \<Rightarrow> block"
  where
    "prev b = b" (* TODO *)

(* Definition 4.25: n'th generation ansectr block *)
fun n_cestor :: "(block * nat) \<Rightarrow> block"
  where
    "n_cestor (b, n) = b" (* TODO *)

(* Definition 4.26: Blockchain membership *)
fun blockchain_membership :: "(block * block) \<Rightarrow> bool" 
  where
    "blockchain_membership (b1, b2) = (\<exists> n. n \<in> \<nat> \<and> b1 = n_cestor(b2, n))"

(* Definition 4.27: Score of a block *)
fun score :: "block * state \<Rightarrow> real"
  where
    "score (b, \<sigma>) = 0.0" (* TODO *)
end