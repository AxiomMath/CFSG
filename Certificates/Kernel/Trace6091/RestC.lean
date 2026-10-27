module

public import Certificates.Kernel.Trace6091.OddC

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.AxisCount
  CFSG.Monster.Existence Finset

theorem pairC : pairScanT PC (betaTabT PC) = 0 := by decide +kernel

theorem pairC_sum : ∑ q ∈ range 276, (xTerm permMonoC 0 (Model.thetaN 0 ^^^ pairD q) +
    xTerm permMonoC 63 (Model.thetaN 63 ^^^ pairD q)) = 0 :=
  (pairScanT_eq pe_PC).symm.trans pairC

theorem pairBadC : pairScanT PBadC (betaTabT PBadC) ≠ 0 := by decide +kernel

theorem wScanC : wScanT PC (betaTabT PC) = 16 := by decide +kernel

theorem wTrC : wTr (Native.GD.ofGen (Native.mkCtx ()) (.perm permMonoC)) = 16 :=
  (wScanT_eq pe_PC).symm.trans wScanC

theorem wScanBadC : wScanT PBadC (betaTabT PBadC) ≠ 16 := by decide +kernel

theorem latTrC : latTr (Native.GD.ofGen (Native.mkCtx ()) (.perm permMonoC)) = 0 := by
  rw [latTr_perm]
  decide +kernel

theorem latTr2C : latTr2 (Native.GD.ofGen (Native.mkCtx ()) (.perm permMonoC)) = 0 := by
  rw [latTr2_perm]
  decide +kernel

end Certificates.Kernel.Trace6091

end
