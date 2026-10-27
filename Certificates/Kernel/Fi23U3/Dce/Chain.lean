module

public import Certificates.Kernel.Fi23U3.Dce.Data
public import Certificates.Kernel.Fi23U3.Dce.CoverData
public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce3

theorem ds_eq : DS = [0, 1, 2, 5, 6, 7, 8, 14, 17, 22, 26, 54, 63, 65, 67, 75, 95, 101, 110, 124,
      132, 184, 190, 209, 250, 329, 337, 346, 356, 467, 565, 812, 1770, 1950] ∧
    CN = [8748, 27, 729, 729, 729, 162, 1458, 1458, 162, 729, 162, 2187, 729, 1458, 729, 729, 4374,
      729, 729, 729, 4374, 729, 2187, 729, 1458, 4374, 729, 729, 729, 2187, 729, 2187, 4374,
      4374] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem stab_ok : stabRange FB INVM 54 RD RW 44010 DS CG CW CB CS CT CN 0 34 = true := by
  decide +kernel

end CFSG.KD.Fi23Dce3

end
