theory CodeGeneration

imports Main CBCCasper

begin

code_printing
  type_constructor bool => (Haskell) "bool"
  | constant True => (Haskell) "true"
  | constant False => (Haskell) "false"

instantiation consensus_value :: equal
begin 

definition "HOL.equal (x ::consensus_value) y \<longleftrightarrow> x = y"
instance  by standard (simp add: equal_consensus_value_def)

end

code_printing
  class_instance consensus_value :: "HOL.equal" => (Haskell) -
  |type_constructor consensus_value => (Haskell) "Map String String"


instantiation validator :: equal
begin 

definition "HOL.equal (x ::validator) y \<longleftrightarrow> x = y"
instance  by standard (simp add: equal_validator_def)

end

code_printing
  class_instance validator :: "HOL.equal" => (Haskell) -
  | type_constructor validator => (Haskell) "Map String String"


export_code is_future_state equivocation in Haskell
  module_name CBCCasper file GeneratedCode


end