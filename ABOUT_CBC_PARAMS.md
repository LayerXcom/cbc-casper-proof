# About CBC Casper parameters
## `params` as a global configuration
TODO

## Sets dependent on the parameters
Isabelle don't support dependent types.

Therefore, corresponding sets are defined in [CBCCasper.thy] and `message`, `state`, etc. types in function definitions are assumes that they are used for correct values.

We need to take care that in these (essentially same) cases, variables need to be limited to the sets.

(1) Quantify variables
(2) Construct a set

even when it's clear from the context that they belongs to a certain set.

For example, here
```
(* Definition 4.6: Latest Message *)
definition latest_message :: "params ⇒ state ⇒ (validator ⇒ state)"
  where
    "latest_message params σ v = {m ∈ M params. m ∈ from_sender params (v, σ) ∧ later_from params (m, v, σ) = ∅}"
```

However, for simplicity, we omit th

About `sender`, `est` etc.
```
(* Definition 4.1: Observed validators *)
definition observed :: "state ⇒ validator set"
  where
    "observed σ = {sender m | m. m ∈ σ}"
```

Also, `ε params σ`
```
(* Definition 7.12 *)
definition is_majority_driven :: "params ⇒ consensus_value_property ⇒ bool"
  where
    "is_majority_driven params p = (∀ σ ∈ Σ params. is_majority params (agreeing_validators params (p, σ), σ) ⟶ (∀ c ∈ ε params σ. p c))"
```
