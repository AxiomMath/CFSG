module

public import Certificates.Kernel.LocalQT.HSAut.K4146R
public import Certificates.Kernel.Misc.Perm.CharsLits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars_lits CFSG.KD.LQT.HN.R1 CFSG.QuasithinUnique.Id2519.HSAut.r1Hex
#kmisc_hexflat CFSG.KD.LQT.HN.R1 CFSG.QuasithinUnique.Id2519.HSAut.r1Hex 3 3850 12 1

namespace CFSG.KD.LQT.HN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN
open CFSG.KD.LQT.C4126 CertificateChecks.KernelSporSch

theorem r1_ok : bAnd(canonK 3850 12 (mask 12) (3850 * 12) (R1.F 0),
    bAnd(invEqK 3850 12 (mask 12) (3850 * 12) (R1.F 0) (R1.F 0),
    bAnd(Nat.beq (pc (R1.F 0) (X 2)) (pc (X 2) (R1.F 0)),
      Nat.beq (pc (R1.F 0) (X 3)) (pc (X 3) (R1.F 0))))) = true := by
  quickRfl

theorem ru_ok : Nat.beq (pc (R1.F 0) (HC.F 0)) (wfoldR ls8 wRU) = true := by quickRfl

theorem t_ok : bAnd(allN 4 (fun b => Nat.beq (img (pc (wfoldR ls8 wT) (R1.F 0)) b) b),
    (Nat.beq (img (pc (wfoldR ls8 wT) (R1.F 0)) 5) 5).not) = true := by
  quickRfl

theorem canon_ok' : bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HC.F 0),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HC.F 6),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HC.F 7),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HS.F 0),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HS.F 1),
      canonK 3850 12 (mask 12) (3850 * 12) (HSI 1)))))) = true := by
  quickRfl

end CFSG.KD.LQT.HN

end
