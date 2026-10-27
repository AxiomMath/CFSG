module

public import Certificates.Kernel.TwistDce3.ON.Data
public import Certificates.Kernel.TwistDce3.ON.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce3

@[expose] def idCodes : List (List Nat) := [[6], [7], [8], [9], [10], [11]]

set_option maxRecDepth 100000 in
theorem letters_ok : lettersOK 14 FO INVM 12 11172 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fb_ok : CFSG.KC.TwDce2.lettersOK FB INVM 57 = true ∧
    CFSG.KC.TwDce2.relsOK FB 57 idCodes = true ∧ repackOK PB F FB 6 57 = true := by
  decide +kernel

end CFSG.KD.ONDce3

end
