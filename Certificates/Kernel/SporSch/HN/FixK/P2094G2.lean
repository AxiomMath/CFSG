module

public import Certificates.Kernel.SporSch.HN.FixK.TabS
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2094_2 (k : Nat) : Bool := fixOkS CFSG.KD.HNPt2094.GA SWGA SJGA SGGA FIX2094 2 k

@[expose] def fixOkR (G W J GO lo n v : Nat) : Bool :=
  Nat.beq (CFSG.KC.LL.HNX.fixSumS CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 16 W J GO
    lo n) v

@[expose] def fix2094_2t (j : Nat) : Bool :=
  fixOkR CFSG.KD.HNPt2094.GA SWGA SJGA SGGA (Nat.add 15589 (Nat.mul 1550 j))
    (Nat.sub 1550 (Nat.mul 876 j)) (Nat.sub 1254 (Nat.mul 18 j))

theorem pre2094_2 : CFSG.KC.LL.HNX.sPreOK CFSG.KD.LgHNX.CM3
    (CFSG.KC.LL.HN.subI (CFSG.KD.HNPt2094.EL 21)) SWGA SJGA SGGA SCGA SDGA = true := by
  quickRfl

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2094_2 CFSG.KD.HNXK.fix2094_2 7
#kss_each CFSG.KD.HNXK.F2094_2T CFSG.KD.HNXK.fix2094_2t 2

end
