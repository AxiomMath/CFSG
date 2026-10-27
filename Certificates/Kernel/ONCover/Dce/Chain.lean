module

public import Certificates.Kernel.ONCover.Dce.Data
public import Certificates.Kernel.ONCover.Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3

theorem ds_eq : DS = [0, 1, 3, 8, 9, 14, 22, 43, 58, 60, 62, 64, 76, 82, 88] ∧
    CN = [1876896, 168, 1876896, 12, 12, 16, 49, 16, 168, 16, 168, 1876896, 1876896, 1876896,
      1876896] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem stab_ok : stabRange FB INVM 57 RD RW 18934 DS CG CW CB CS CT CN 0 15 = true := by
  decide +kernel

end CFSG.KD.ONCoverDce3

end
