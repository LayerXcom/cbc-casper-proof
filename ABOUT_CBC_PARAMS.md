# About CBC Casper parameters
## `params` as a global configuration
Each member of the CBC Casper family of protocols is going to be identified by five "parameters" (See section 2.1 of the paper) and the asynchronous safety is proved for arbitray parameters.

To leverage this feature, we defined `params` type and `is_valid_params` function so that we can prove lemmas and theorems for all valid parameters like:

```
(* Lemma 1 *)
lemma monotonic_futures :
  "∀ params σ' σ. is_valid_params params ∧ σ' ∈ Σt params ∧ σ ∈ Σt params
   ⟶ σ' ∈ futures params σ ⟷ futures params σ' ⊆ futures params σ"
```

We can extract each parameter by functions defined in [CBCCasper.thy] which receives `params` and returns a certain parameter. For example, this function returns the validator set.

```
fun V :: "params ⇒ validator set"
  where
    "V (Params (v_set, _, _, _, _)) = v_set"
```

## Sets dependent on the parameters
Isabelle doesn't support dependent types so we can't define `M` (messages) and `Σ` (states) as types because they depends on `params`. Therefore, we defined functions which receives `params` and returns sets corresponding to `M` and `Σ` in [CBCCasper.thy].

Note that `validator`, `consensus_value`, `message` and `state` types are different from the "valid" sets returned by `V`, `C`, `M` and `Σ`. Fow now, functions defined to receive these types assumes that they are used only for elements exist in these "valid" sets. We can fix these functions so that they return `undefined` if they receives invalid values.

We need to take care that in these (essentially same) cases, variables need to be limited to the sets even when it's clear from the context.

(1) Quantify variables
(2) Construct a set

For example, here it's assumed that `σ` is in `Σ params` and `σ'` is limited to the one in the set `Σt params`.
```
(* Definition 3.1 *)
fun futures :: "params ⇒ state ⇒ state set"
  where
    "futures params σ = {σ' ∈ Σt params. is_faults_lt_threshold params σ' ∧ is_future_state (σ', σ)}"
```

As exceptions, for simplicity, we omit these requirements when we use `sender`, `est`, `justification` amd `ε` because it's obvious they returns valid values when they received valid messages. For example, 

```
(* Definition 7.12 *)
definition is_majority_driven :: "params ⇒ consensus_value_property ⇒ bool"
  where
    "is_majority_driven params p = (∀ σ ∈ Σ params. is_majority params (agreeing_validators params (p, σ), σ) ⟶ (∀ c ∈ ε params σ. p c))"
```
