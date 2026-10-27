module

public import Certificates.Kernel.S63K.OData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Data.Kernel.S63K.GeoK
public import Certificates.Data.Kernel.SporSch.TitsPrim
public import Certificates.Data.D4HexOverCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.OK

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.Prim CFSG.D4Hex
  CertificateChecks.KernelS63 CertificateChecks.KernelS63.HD

@[expose] noncomputable def bI (i : Nat) : Nat := nIf(Nat.beq i 3, 6, nIf(Nat.beq i 4, 8, i))
@[expose] noncomputable def GB (i : Nat) : Nat := OD.D (bI i)
@[expose] noncomputable def uI (i : Nat) : Nat := nIf(Nat.beq i 3, 6, i)
@[expose] noncomputable def GU (i : Nat) : Nat := PA (uI i)
@[expose] noncomputable def fl (j c : Nat) : Nat := pgW 13 (OD.D j) c
@[expose] noncomputable def lf (i : Nat) : Nat := pg 12 (mask 12) LT i
@[expose] noncomputable def posF (l p : Nat) : Nat :=
  nIf(Nat.beq (lf (3 * l)) p, 0, nIf(Nat.beq (lf (3 * l + 1)) p, 1, 2))
@[expose] noncomputable def zt (x : Nat) : Nat := ptW [3, 2, 4, 2] x
@[expose] noncomputable def zIt : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun _ ih x => zt (ih x))

theorem ch4238F : (allN 8 fun j => allN 7371 fun c => strictB (fl j c) fun f =>
    bAnd(Nat.blt (f / 3) 2457, bAnd(Nat.beq (keyF lf (f / 3))
      (sortKeyF (im j (lf (3 * (c / 3)))) (im j (lf (3 * (c / 3) + 1)))
        (im j (lf (3 * (c / 3) + 2)))),
      Nat.beq f (3 * (f / 3) + posF (f / 3) (im j (lf c)))))) = true := by
  quickRfl

theorem ch4238Z : (allN 7371 fun c => Nat.beq (pgW 13 (OD.D 8) c) (fl 3 (fl 2 (fl 4 (fl 2 c))))) =
    true := by
  quickRfl

theorem ch4238C : bAnd(allN 8 (fun i => canonK 7371 13 (mask 13) (7371 * 13) (OD.D i)),
    bAnd(allN 5 (fun i => canonK 7371 13 (mask 13) (7371 * 13) (GB i)),
      allN 4 (fun i => canonK 819 12 (mask 12) (819 * 12) (GU i)))) = true := by
  quickRfl

theorem ch4238R : bAnd(Nat.beq (pg 13 (mask 13) (OD.D 31) 0) 0,
    bAnd(allN 12 (fun c => Nat.beq (pg 13 (mask 13) (OD.D 32) c) (ovReps.getD c 0)),
      allN 6 (fun c => Nat.beq (pg 12 (mask 12) (OD.D 33) c) (ovURep.getD c 0)))) = true := by
  quickRfl

theorem ch4238D : bAnd(bfsTK 7371 13 OD.D 8 1 (OD.D 31) 7371 (OD.D 9) (OD.D 10) (OD.D 11)
      (OD.D 12) (OD.D 13) (OD.D 14) (OD.D 15),
    labOKK 7371 13 OD.D 8 1 (OD.D 12) (OD.D 31) (OD.D 13) (OD.D 14) (OD.D 15)) = true := by
  quickRfl

theorem ch4238B : bAnd(bfsTK 7371 13 GB 5 12 (OD.D 32) 7371 (OD.D 16) (OD.D 17) (OD.D 18)
      (OD.D 19) (OD.D 20) (OD.D 21) (OD.D 22),
    labOKK 7371 13 GB 5 12 (OD.D 19) (OD.D 32) (OD.D 20) (OD.D 21) (OD.D 22)) = true := by
  quickRfl

theorem ch4238U : bAnd(bfsTK 819 12 GU 4 6 (OD.D 33) 819 (OD.D 23) (OD.D 24) (OD.D 25)
      (OD.D 26) (OD.D 27) (OD.D 28) (OD.D 29),
    labOKK 819 12 GU 4 6 (OD.D 26) (OD.D 33) (OD.D 27) (OD.D 28) (OD.D 29)) = true := by
  quickRfl

theorem ch4238L : bAnd(Nat.beq (pgW 13 (OD.D 19) 2) 1,
    bAnd(allN 7371 (fun c => !(lf c == 0) || pgW 13 (OD.D 19) c == 0 || pgW 13 (OD.D 19) c == 2),
    bAnd(Nat.beq (pgW 12 (OD.D 26) 5) 1, bAnd(Nat.beq (lf 3) 0,
      allN 6 (fun c => Nat.beq (cntK 819 12 (OD.D 26) c) ([1, 2, 16, 32, 256, 512].getD c 0))))))
    = true := by
  quickRfl

theorem ch4238Zt : bAnd(Nat.beq (zt 0) 0, bAnd(Nat.beq (sortKeyF (zt 0) (zt 1) (zt 5)) 824,
    bAnd(allN 819 (fun x => zIt 7 x == x && zt (im 0 x) == im 2 (zt x) &&
      zt (im 1 x) == ptW [0, 1] (zt x) && zt (im 2 x) == ptW [1, 2] (zt x) &&
      zt (im 6 x) == ptW [0, 2, 6, 0, 2] (zt x)),
    bAnd(!(allN 819 fun x => zt (im 0 x) == im 0 (zt x)),
    bAnd(!(im 7 0 == 0), bAnd(Nat.beq (sortKeyF (im 7 0) (im 7 1) (im 7 5)) 824,
    bAnd(Nat.beq (im 3 0) 0, !(sortKeyF (im 3 0) (im 3 1) (im 3 5) == 824)))))))) =
    true := by
  quickRfl

end CertificateChecks.KernelS63.OK

end
