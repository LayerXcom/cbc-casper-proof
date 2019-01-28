theory TFGCasper

imports Main HOL.Real CBCCasper ConsensusSafety ExampleProtocols

begin

(* Section 4.4: Casper the Friendly GHOST *)
(* Definition 4.23: Blocks *)
type_synonym block = consensus_value

locale Ghost = Protocol +
  fixes Genesis :: block
  and NextBlkgen :: "block \<Rightarrow> block set"

fun (in Ghost) B_i :: "nat \<Rightarrow> block set"
  where
    "B_i 0 = {Genesis}"
  | "B_i n = \<Union> {NextBlkgen b | b. b \<in> B_i (n - 1)}"

definition (in Ghost) B :: "block set"
  where
    "B = \<Union> (B_i ` \<nat>)"

(* Definition 4.24: Previous block resolver *)
fun (in Ghost) prev :: "block \<Rightarrow> block set"
  where
    "prev b = (if b = Genesis then {b} else {b'. b' \<in> NextBlkgen b})"

(* Definition 4.25: n'th generation ansectr block *)
fun (in Ghost) n_cestor :: "block \<Rightarrow> nat \<Rightarrow> block set"
  where
    "n_cestor b 0 = {b}"
  | "n_cestor b n = {b. \<forall> prevblk. prevblk \<in> (prev b) \<and> (b \<in> n_cestor prevblk (n-1))}"

(* Definition 4.26: Blockchain membership *)
fun (in Ghost) blockchain_membership :: "block * block \<Rightarrow> bool"
  where
    "blockchain_membership (b1, b2) = (\<exists> n. n \<in> \<nat> \<and> (b1 \<in> n_cestor b2 n))"

(* Definition 4.27: Score of a block *)
fun (in Ghost) score :: "block * state \<Rightarrow> real"
  where
    "score (b, \<sigma>) = sum W ({v. \<forall> v. \<exists> b'. v \<in> V \<and> b' \<in> (latest_estimates_from_non_equivocating_validators \<sigma> v) \<and> (blockchain_membership (b, b'))})"

(* Definition 4.28: Children *)
fun single_est_set :: "message \<Rightarrow> block set"
  where
    "single_est_set m = {b . b = est m}"

fun (in Ghost) children :: "block * state \<Rightarrow> block set"
  where
    "children (b, \<sigma>) = {b'. \<forall> b'. \<forall> m. m \<in> \<sigma> \<and> b' \<in> \<Union> (single_est_set ` \<sigma>) \<and> (b \<in> prev b')}"
    (* same meaning? *)
    (* "children (b, \<sigma>) = {b'. \<forall> b'. (b' \<in> est ` \<sigma>) \<and> (b \<in> prev b')}" *)

(* Definition 4.29: Best Children *)
fun (in Ghost) best_children :: "block * state \<Rightarrow>  block set"
  where
    "best_children (b, \<sigma>) = {b'. \<forall> b'.
    (b' \<in> children (b, \<sigma>)) \<and>
    \<not> (\<exists> b''. (b'' \<in> children (b, \<sigma>)) \<and> (score (b'', \<sigma>)) > (score (b', \<sigma>)))}"

(* Definition 4.30: GHOST *)
function (in Ghost) GHOST :: "(block set) * state => block set"
  where
    "GHOST (b_set, \<sigma>) =
    (\<Union> {s. \<forall> b. s = GHOST ((best_children (b, \<sigma>)), \<sigma>) \<and> b \<in> b_set \<and> (children (b, \<sigma>) \<noteq> \<emptyset>)})
    \<union>
    (\<Union> {s. \<forall> b. s = {b} \<and> b \<in> b_set \<and> (children (b, \<sigma>) = \<emptyset>)})"
  by auto

(* Definition 4.31: Casper the Friendly Ghost *)
fun (in Ghost) estimator :: "state \<Rightarrow> block set"
  where
    "estimator \<sigma> = GHOST ({Genesis}, \<sigma>)"

(* Definition 4.32: Example non-trivial properties of consensus values *)
fun (in Ghost) P :: "consensus_value_property set \<Rightarrow> block set \<Rightarrow> consensus_value_property set"
  where
    "P p_set b_set = {p. \<exists>!b. \<forall>b'. b \<in> b_set \<and> b' \<in> b_set \<and> (blockchain_membership (b, b') \<longrightarrow> p b' = True) \<and> \<not> (blockchain_membership (b, b') \<longrightarrow> p b' = False) }"

end
