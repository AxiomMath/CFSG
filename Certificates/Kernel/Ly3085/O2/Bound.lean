module

public import Certificates.Kernel.Ly3085.O2.Data
public import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.LyO2

theorem kxBound : ∀ b < 15137, Nat.blt (KX b) (2 ^ 196608) = true := by
  kc_cover 512

end CFSG.KD.LyO2

end
