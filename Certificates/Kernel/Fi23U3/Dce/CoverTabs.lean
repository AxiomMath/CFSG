module

public import Certificates.Kernel.Fi23U3.Dce.Data
public import Certificates.Kernel.Fi23U3.Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Tuple

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce3

@[expose] def idCodes : List (List Nat) := [[6], [7], [8], [9], [10], [11]]

set_option maxRecDepth 100000 in
theorem letters_ok : lettersOK 14 FO INVM 12 8748 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fb_ok : CFSG.KC.TwDce2.lettersOK FB INVM 54 = true ∧ repackOK PB F FB 12 54 = true ∧
    relsOK PB F 54 idCodes = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tuple_ok : tupleOK 14 FO PB F TU BS NB 12 8748 54 = true := by
  decide +kernel

end CFSG.KD.Fi23Dce3

end
