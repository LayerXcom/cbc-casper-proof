# Design of CBC Casper in Isabelle
## `params` as a global configuration
Each member of the CBC Casper family of protocols is going to be identified by five "parameters" (See section 2.1 of the paper) and the asynchronous safety is proved for arbitray parameters.

To leverage this feature, we defined `Protocol` locale so that we can prove lemmas and theorems for all valid parameters.

```
locale Protocol =
  fixes V :: "validator set"
  and W :: weight
  and t :: threshold
  and C :: "consensus_value set"
  and ε :: "message set ⇒ consensus_value set"
  and Σ :: "state set"
  and M :: "message set"

  assumes W_type: "⋀w. w ∈ range W ⟹ w > 0"
  and t_type: "0 ≤ t" "t < Sum (W ` V)"
  and C_type: "card C > 1"
  and ε_type: "⋀s. s ∈ Σ ⟹ ε s ∈ Pow C - {∅}"

  assumes Σ_def: "Σ = (⋃i∈ℕ. Σ_i (V,C,ε) i)"
  and M_def: "M = (⋃i∈ℕ. M_i (V,C,ε) i)"
begin
```

```
(* Lemma 1 *)
lemma (in Protocol) monotonic_futures :
  "∀ σ' σ. σ' ∈ Σt ∧ σ ∈ Σt
   ⟶ σ' ∈ futures σ ⟷ futures σ' ⊆ futures σ"
  by auto
```

## Sets dependent on the parameters
Isabelle doesn't support dependent types so we can't define the CBC parameters as types. Therefore, note that `validator`, `consensus_value`, `message` and `state` types are different from the types defined in the paper. Instead, `V`, `C`, `M` and `Σ` represent them as sets. Fow now, functions defined to receive these types assumes that they are used only for elements exist in these "valid" sets. 

For this reason, we need to take care these things.
variables need to be forced to be in these sets or it need to be proved that they .

(1) When we quantify a variable with `∀` or `∃`, a condition that the variable exists in the sets corresponding to the type.
(2) Sets returned by functions must be a subset of the sets corresponding to the type. These functions need to be defined like this proved to return correct sets.

For example, in `futures` functions, it's assumed that the received `σ` is in `Σ` and the returned sets are defined to be a subset of `Σt`.
```
fun (in Protocol) futures :: "state ⇒ state set"
  where
    "futures σ = {σ' ∈ Σt. is_future_state (σ', σ)}"
```

On the other hand, it's **proved** that the function `observed` returns correct set.
```
definition (in Protocol) observed :: "state ⇒ validator set"
  where
    "observed σ = {sender m | m. m ∈ σ}"

lemma (in Protocol) oberved_type :
  "∀ σ ∈ Σ. observed σ ⊆ V"
  using Protocol.M_type Protocol_axioms observed_def state_is_subset_of_M by fastforce
```