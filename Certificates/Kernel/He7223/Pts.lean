module

public import Certificates.Data.Kernel.Misc.WordPts
public import Certificates.Kernel.He7223.Words
public import Certificates.Kernel.He7223.GL
public import Certificates.Kernel.LocalComp.HeFix
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7223

open CFSG.KLie.CT CFSG.KC.WordPts CertificateChecks.KernelLC.HeFix

@[expose] def bsL : List Nat := [0, 1, 2, 3, 4]

@[expose] def bBL : List Nat := [2464, 7750, 8271, 8281, 5830, 6837]

@[expose] def NJ : List Nat := [14902707730, 61034850803]

@[expose] noncomputable def gw (j : Nat) : List Int := GW.getD j []

@[expose] noncomputable def lg (j : Nat) : List Int := LG.getD j []

@[expose] noncomputable def matE (g : List Int) (M : Nat) : Bool := matK 8330 14 LU LUI bsL EB 6 g M

@[expose] noncomputable def matQ (g : List Int) (M : Nat) : Bool := matK 8330 14 LU LUI bsL QB 4 g M

@[expose] noncomputable def permBK (g : List Int) (M : Nat) : Bool :=
  allN 6 fun i => CFSG.KC.M1F2.strictB (evW 8330 14 LU LUI g (bBL.getD i 0)) fun q =>
    allN 6 fun r => Bool.rec (motive := fun _ => Bool)
      (notB (Nat.beq q (bBL.getD r 0))) (Nat.beq q (bBL.getD r 0))
      (bit (CFSG.KC.WordPts.colF 6 M i) r)

theorem ch7223eb : ebK 8330 14 LU LUI bsL EB 6 = true := by quickRfl

theorem ch7223qb : ebK 8330 14 LU LUI bsL QB 4 = true := by quickRfl

theorem ch7223mNs0 : matE (gw 0) (gen NS 0) = true := by quickRfl

theorem ch7223mNs1 : matE (gw 1) (gen NS 1) = true := by quickRfl

theorem ch7223mL0 : matE (lg 0) (gen LS 0) = true := by quickRfl

theorem ch7223mL1 : matE (lg 1) (gen LS 1) = true := by quickRfl

theorem ch7223mL2 : matE (lg 2) (gen LS 2) = true := by quickRfl

theorem ch7223mNj0 : matE (gw 4) (gen NJ 0) = true := by quickRfl

theorem ch7223mNj1 : matE (gw 5) (gen NJ 1) = true := by quickRfl

theorem ch7223mN70 : matQ (gw 2) (gen N7 0) = true := by quickRfl

theorem ch7223mN71 : matQ (gw 3) (gen N7 1) = true := by quickRfl

theorem ch7223y5 : andB (fixPtsK 8330 14 LU LUI bsL [gw 6, gw 6, gw 6, gw 6, gw 6])
    (notB (fixPtsK 8330 14 LU LUI bsL [gw 6])) = true := by quickRfl

theorem ch7223tc : andB (conjPtsK 8330 14 LU LUI bsL (gw 7) (gw 8) [gw 8]) (
    andB (conjPtsK 8330 14 LU LUI bsL (gw 9) (gw 8) [gw 8])
      (conjPtsK 8330 14 LU LUI bsL (gw 10) (gw 8) [gw 8])) = true := by quickRfl

theorem ch7223eL : eqPtsK 8330 14 LU LUI bsL [lg 0, lg 1, lg 0, lg 1] (selW EB 63) = true := by
  quickRfl

theorem ch7223eB : allN 6 (fun i => fixPtsK 8330 14 LU LUI bBL [EB.getD i []]) = true := by
  quickRfl

theorem ch7223lB : andB (permBK (lg 0) (gen BB 0)) (andB (permBK (lg 1) (gen BB 1))
    (permBK (lg 2) (gen BB 2))) = true := by quickRfl

end CertificateChecks.KernelHe7223

end
