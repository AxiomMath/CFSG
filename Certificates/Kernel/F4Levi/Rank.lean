module

public import Certificates.Kernel.F4Levi.Data
public import Certificates.Kernel.F4Inv.Rank

public section

namespace CFSG.KD.F4Levi

open CFSG.KC.F4Rank

theorem k0_ok : rankSubChk CFSG.KD.F4Inv.u26 (es.getD (ra.getD 0 0) 0) k0 = true := by
  decide +kernel

theorem k2_ok : rankChk (es.getD (ra.getD 2 0) 0) k2 = true := by decide +kernel

theorem k0_length : k0.length = 18 ∧ k2.length = 36 := by decide +kernel

end CFSG.KD.F4Levi

end
