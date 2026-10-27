module

public import Certificates.Kernel.SporSch.J3K426.Text
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.PkPow
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.Misc.Perm.HexWordsCmd
public meta import Certificates.Data.K426J3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J3KT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.RankThree.PartTwo.KFacts.K426

@[expose] noncomputable def X0 : Nat := F 18

@[expose] noncomputable def X1 : Nat := F 19

@[expose] noncomputable def D (l : Nat) : Nat := F (37 + l)

@[expose] noncomputable def DI (l : Nat) : Nat := pinvS 6156 13 (mask 13) (D l)

@[expose] noncomputable def G : Nat := F 39

@[expose] noncomputable def L (j : Nat) : Nat := F (5 + j)

@[expose] noncomputable def U : Nat := wv 6156 13 D DI j3tWu

@[expose] noncomputable def V : Nat := wv 6156 13 D DI j3tWv

@[expose] noncomputable def UV (m : Nat) : Nat :=
  pcomp 6156 13 (mask 13) (ppw 6156 13 U (m / 3)) (ppw 6156 13 V (m % 3))

@[expose] noncomputable def E27 (m : Nat) : Nat :=
  pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) (ppw 6156 13 (L 2) (m / 9))
    (ppw 6156 13 (L 4) (m / 3 % 3))) (ppw 6156 13 (L 0) (m % 3))

meta def fiArr : Array Nat := CFSG.KC.Misc.HexWords.invs j3tHex 4 6156 13 40

meta def fwArr : Array Nat := CFSG.KC.Misc.HexWords.words j3tHex 4 6156 13 40
  ["", "5", "5 5", "9", "9 5", "9 5 5", "9 9", "9 9 5", "9 9 5 5",
   "7", "7 5", "7 5 5", "7 9", "7 9 5", "7 9 5 5", "7 9 9", "7 9 9 5", "7 9 9 5 5",
   "7 7", "7 7 5", "7 7 5 5", "7 7 9", "7 7 9 5", "7 7 9 5 5", "7 7 9 9", "7 7 9 9 5", "7 7 9 9 5 5"]

#kc_nattree CertificateChecks.KernelSporSch.J3KT.FI fiArr

#kc_nattree CertificateChecks.KernelSporSch.J3KT.FW fwArr

theorem szOK' : szOK 6156 13 = true := by quickRfl

theorem perm : allN 40 (fun j => permOK 6156 13 (mask 13) (6156 * 13) (F j) (FI j)) = true := by
  quickRfl

theorem inv1 : Nat.beq (pcomp 6156 13 (mask 13) G X0)
    (pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) X0 X0) G) = true := by quickRfl

theorem inv2 : Nat.beq (pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) G (D 0))
    (pcomp 6156 13 (mask 13) G (D 0))) (pidn 6156 13) = true := by quickRfl

theorem comm : allN 2 (fun l => Nat.beq (pcomp 6156 13 (mask 13) X0 (D l))
    (pcomp 6156 13 (mask 13) (D l) X0)) = true := by quickRfl

theorem u3 : Nat.beq (ppw 6156 13 U 3) (pidn 6156 13) = true := by quickRfl

theorem v3 : Nat.beq (ppw 6156 13 V 3) (pidn 6156 13) = true := by quickRfl

theorem uvDist : allN 9 (fun m => allN m (fun m' => bIf(Nat.beq (UV m) (UV m'), false, true))) =
    true := by quickRfl

theorem uvFix : allN 9 (fun m => bIf(Nat.beq m 0, true, Nat.beq (nfix 6156 13 (UV m)) 0)) =
    true := by quickRfl

theorem lc1 : Nat.beq (pcomp 6156 13 (mask 13) (L 2) (L 4)) (pcomp 6156 13 (mask 13) (L 4) (L 2)) =
    true := by quickRfl

theorem lc2 : Nat.beq (pcomp 6156 13 (mask 13) (L 2) (L 0)) (pcomp 6156 13 (mask 13) (L 0) (L 2)) =
    true := by quickRfl

theorem lc3 : Nat.beq (pcomp 6156 13 (mask 13) (L 4) (L 0)) (pcomp 6156 13 (mask 13) (L 0) (L 4)) =
    true := by quickRfl

theorem eW : allN 27 (fun m => Nat.beq (FW m) (E27 m)) = true := by quickRfl

theorem eFix : allN 27 (fun m => bIf(Nat.beq m 0, true,
    Nat.beq (nfix 6156 13 (FW m)) (nIf(Nat.beq (m % 3) 0, 0, 36)))) = true := by quickRfl

theorem eDist : allN 27 (fun m => allN m (fun m' => bIf(Nat.beq (FW m) (FW m'), false, true))) =
    true := by quickRfl

theorem rFix : bAnd(Nat.beq (nfix 6156 13 X0) 36, Nat.beq (nfix 6156 13 X1) 0) = true := by
  quickRfl

theorem sw0 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [2, -5] (L 2) = true := by
  quickRfl

theorem sw1 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5
    [3, 2, -3, 5, 3, 3, 2, 3, 3, 1, -3, 1, 3, 4] (L 4) = true := by quickRfl

theorem sw2 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 [5] (L 0) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J3KT

end
