theory CodeGenerator

imports Main CBCCasper

begin

export_code is_future_state in Haskell
  module_name CBCCasper file GeneratedCode

end