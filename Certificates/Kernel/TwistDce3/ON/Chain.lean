module

public import Certificates.Kernel.TwistDce3.ON.Data
public import Certificates.Kernel.TwistDce3.ON.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce3

theorem ds_eq : DS = [0, 1, 3, 8, 9, 12, 19] ∧
    CN = [1876896, 168, 1876896, 36, 36, 16, 147] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem stab_ok : stabRange FB INVM 57 RD RW 4625 DS CG CW CB CS CT CN 0 7 = true := by
  decide +kernel

end CFSG.KD.ONDce3

end
