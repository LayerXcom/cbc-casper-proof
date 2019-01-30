theory TFGCasper

imports Main HOL.Real CBCCasper ConsensusSafety ExampleProtocols

begin

(* Section 4.4: Casper the Friendly GHOST *)
(* Definition 4.23: Blocks *)
type_synonym block = consensus_value

fun B_i :: "(block * (block \<Rightarrow> block set)) \<Rightarrow> nat \<Rightarrow> block set"
  where
    "B_i (g, blk_gen) 0 = {g}"
  | "B_i (g, blk_gen) n = \<Union> {blk_gen b | b. b \<in> B_i (g, blk_gen) (n - 1)}"

locale Ghost = Protocol +
  fixes genesis :: block
  fixes B :: "block set"
  and block_generator :: "block \<Rightarrow> block set"

  assumes B_def : "B = \<Union> (B_i (genesis, block_generator)` \<nat>)"
  and block_generator_type : "\<forall> b \<in> B. is_singleton {b' \<in> B. b \<in> block_generator b'}"

(* Definition 4.24: Previous block resolver *)
fun (in Ghost) prev :: "block \<Rightarrow> block"
  where
    "prev b = (if b = genesis then b else the_elem {b' \<in> B. b \<in> block_generator b'})"

(* Definition 4.25: n'th generation ancestor block *)
fun (in Ghost) n_cestor :: "block * nat \<Rightarrow> block"
  where
    "n_cestor (b, 0) = b"
  | "n_cestor (b, n) = n_cestor (prev b, n-1)"

(* Definition 4.26: Blockchain membership *)
fun (in Ghost) blockchain_membership :: "block \<Rightarrow> block \<Rightarrow> bool" (infixl "\<downharpoonright>" 70)
  where
    "b1 \<downharpoonright> b2 = (\<exists> n. n \<in> \<nat> \<and> b1 = n_cestor (b2, n))"

notation (ASCII)
  comp  (infixl "blockchain_membership" 70)

(* Definition 4.27: Score of a block *)
fun (in Ghost) score :: "state \<Rightarrow> block \<Rightarrow> real"
  where
    "score \<sigma> b = sum W {v \<in> V. \<exists> b' \<in> B. b' \<in> (latest_estimates_from_non_equivocating_validators \<sigma> v) \<and> (b \<downharpoonright> b')}"

(* Definition 4.28: Children *)
fun (in Ghost) children :: "block * state \<Rightarrow> block set"
  where
    "children (b, \<sigma>) = {b' \<in> B. b' \<in> est `\<sigma> \<and> b = prev b'}"

(* Definition 4.29: Best Children *)
fun (in Ghost) best_children :: "block * state \<Rightarrow>  block set"
  where
    "best_children (b, \<sigma>) = {arg_max_on (score \<sigma>) (children (b, \<sigma>))}"

(* Definition 4.30: GHOST *)
function (in Ghost) GHOST :: "(block set * state) => block set"
  where
    "GHOST (b_set, \<sigma>) =
      (\<Union> b \<in> {b \<in> b_set. children (b, \<sigma>) \<noteq> \<emptyset>}. GHOST (best_children (b, \<sigma>), \<sigma>))
       \<union> {b \<in> b_set. children (b, \<sigma>) = \<emptyset>}"
  by auto

(* Definition 4.31: Casper the Friendly Ghost *)
fun (in Ghost) estimator :: "state \<Rightarrow> block set"
  where
    "estimator \<sigma> = GHOST ({genesis}, \<sigma>)"

(* Definition 4.32: Example non-trivial properties of consensus values *)
abbreviation (in Ghost) P :: "consensus_value_property set"
  where
    "P \<equiv> {p. \<exists>!b \<in> B. \<forall>b' \<in> B. (b \<downharpoonright> b' \<longrightarrow> p b' = True) \<and> \<not> (b \<downharpoonright> b' \<longrightarrow> p b' = False)}"
end