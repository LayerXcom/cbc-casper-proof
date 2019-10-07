theory CodeGeneration

imports Main CBCCasper Inspector

begin


definition member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where
    [code del]: "member xs x \<longleftrightarrow> x \<in> set xs"

(* Here, we use ByteString as an internal representation. *)
code_printing code_module Params \<rightharpoonup> (Haskell)\<open>
import qualified Data.ByteString as BS;
import qualified Data.Map as M;

newtype ConsensusValue = ConsensusValue (M.Map BS.ByteString BS.ByteString);
newtype Validator = Validator (M.Map BS.ByteString BS.ByteString);
\<close>

instantiation consensus_value :: equal
begin 

definition "HOL.equal (x ::consensus_value) y \<longleftrightarrow> x = y"
instance  by standard (simp add: equal_consensus_value_def)

end

code_printing
  type_constructor consensus_value => (Haskell) "Params.ConsensusValue"


instantiation validator :: equal
begin 

definition "HOL.equal (x ::validator) y \<longleftrightarrow> x = y"
instance  by standard (simp add: equal_validator_def)

end

code_printing
  type_constructor validator => (Haskell) "Params.Validator"

interpretation p: Params V W t C \<epsilon> for V W t C \<epsilon>
  done

(* Define a constant *)
definition "inspector = p.inspector"

(* FIXME: Wellsortedness error *)
export_code inspector in Haskell
  module_name Insepctor file "GeneratedCode/src"

(* FIXME: Wellsortedness error *)
(* 
interpretation gp: BlockchainParams V W t C \<epsilon> genesis B prev for V W t C \<epsilon> genesis B prev
  done

definition "best_children = gp.best_children"
export_code best_children in Haskell
  module_name TFGCasper file GeneratedCode
*)

(* FIXME: No code equations for GhostParams.GHOST *)
(*
definition "estimator = gp.estimator"
export_code estimator in Haskell
  module_name TFGCasper file GeneratedCode
*)

end