module

public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXChunk
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KD.HNPt2094 CFSG.KD.LgHNX CFSG.KC.Enum CFSG.KC.LL

@[expose] noncomputable def wj (K : Nat) : Nat := fldW WJ (Nat.mul 4 K) 4

@[expose] noncomputable def wi (K : Nat) : Nat := fldW WI (Nat.mul 14 K) 14

@[expose] noncomputable def n2 (j : Nat) : Nat := fldW NN2 (Nat.mul 14 j) 14

@[expose] noncomputable def f2c (m : Nat) : Bool := ptsImg TX MS CM3 M (TT 34) (sliceP PL2 m)
  (sliceP PL2 m) (cntP 8800 m)

@[expose] noncomputable def g2c (m : Nat) : Bool := ptsImg TX MS CM3 M (TT (Nat.add 35 0))
  (sliceP (FL2 0) m) (sliceP (QL2 0) m) (cntP (n2 0) m)

end CertificateChecks.KernelSporSch.HNPt2094

#kss_each CertificateChecks.KernelSporSch.HNPt2094.F2 CertificateChecks.KernelSporSch.HNPt2094.f2c 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G2 CertificateChecks.KernelSporSch.HNPt2094.g2c 137

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KD.HNPt2094 CFSG.KD.LgHNX CFSG.KC.Enum CFSG.KC.LL

theorem fix2 : allN 138 (fun m => ptsImg TX MS CM3 M (TT 34) (sliceP PL2 m) (sliceP PL2 m)
    (cntP 8800 m)) = true := CFSG.KS.PackFld.allN_of_forall F2.all

theorem fix0 : allN 6 (fun j => allN 1 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 35 j))
    (sliceP PL2 m) (sliceP PL2 m) (cntP 1 m))) = true := by quickRfl

theorem gen2 : allN 6 (fun j => allN ((n2 j + 63) / 64) (fun m => ptsImg TX MS CM3 M
    (TT (Nat.add 35 j)) (sliceP (FL2 j) m) (sliceP (QL2 j) m) (cntP (n2 j) m))) = true := by
  refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
  match j, hj with
  | 0, _ =>
    have e : (n2 0 + 63) / 64 = 137 := by decide +kernel
    rw [e]
    exact CFSG.KS.PackFld.allN_of_forall G2.all
  | 1, _ => quickRfl
  | 2, _ => quickRfl
  | 3, _ => quickRfl
  | 4, _ => quickRfl
  | 5, _ => quickRfl
  | _ + 6, h => exact absurd h (by omega)

theorem cov2 : allN 8799 (fun K => Nat.blt (wj K) 6 && Nat.blt (wi K) (n2 (wj K)) &&
    Nat.beq (fldW (FL2 (wj K)) (Nat.mul 21 (wi K)) 21) (fldW PL2 (Nat.mul 21 (Nat.add K 1)) 21) &&
    Bool.not (Nat.beq (fldW (QL2 (wj K)) (Nat.mul 21 (wi K)) 21)
      (fldW PL2 (Nat.mul 21 (Nat.add K 1)) 21))) = true := by quickRfl

theorem q2_lt : allN 6 (fun j => allN (n2 j) (fun i =>
    Nat.blt (fldW (QL2 j) (Nat.mul 21 i) 21) 1140000)) = true := by quickRfl

theorem neg_gen2 : Bool.not (ptsImg TX MS CM3 M (TT 35) (sliceP (FL2 0) 0) (sliceP (FL2 0) 0) 64) =
    true := by
  quickRfl

theorem neg_cov2 : Bool.not (Nat.beq (fldW (FL2 (wj 0)) (Nat.mul 21 (wi 0)) 21)
    (fldW PL2 (Nat.mul 21 2) 21)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2094

end
