module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.PtC
public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXPrim
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.HNPt2094 CFSG.KC.LL CFSG.KC.Enum

theorem v_EL : allN 41 (fun k => validHN (EL k)) = true := by quickRfl

theorem e_EL0 : Nat.beq (EL 0) (CFSG.KD.HNPtC.GT 10) = true := by quickRfl

theorem w_EL : allN 40 (fun k => Nat.beq (wordC CFSG.KD.HNPt.R (ecF (Nat.add k 1)))
    (EL (Nat.add k 1))) = true := by quickRfl

@[expose] noncomputable def ttOK (k : Nat) : Bool := Nat.beq (trM (EL k)) (TT k)

end CertificateChecks.KernelSporSch.HNPt2094

#kss_each CertificateChecks.KernelSporSch.HNPt2094.TTc
  CertificateChecks.KernelSporSch.HNPt2094.ttOK 41

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.HNPt2094 CFSG.KC.LL CFSG.KC.Enum

theorem t_TT : allN 41 (fun k => Nat.beq (trM (EL k)) (TT k)) = true :=
  CFSG.KS.PackFld.allN_of_forall TTc.all

theorem g_fix : Nat.beq (trM (CFSG.KC.LL.HN.subI (EL 0))) GC = true ∧
    Nat.beq (trM (CFSG.KC.LL.HN.subI (EL 20))) G4 = true ∧
    Nat.beq (trM (CFSG.KC.LL.HN.subI (EL 21))) GA = true ∧
    Nat.beq (trM (CFSG.KC.LL.HN.subI (EL 34))) G2 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem comm : Nat.beq (CFSG.KC.LL.HN.mm (EL 19) (EL 20)) (CFSG.KC.LL.HN.mm (EL 20) (EL 19)) = true ∧
    Nat.beq (CFSG.KC.LL.HN.mm (EL 32) (EL 21)) (CFSG.KC.LL.HN.mm (EL 21) (EL 32)) = true ∧
    Nat.beq (CFSG.KC.LL.HN.mm (EL 33) (EL 21)) (CFSG.KC.LL.HN.mm (EL 21) (EL 33)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

theorem seeds : Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KD.HNPt.R 34) (CFSG.KD.HNPt.R 34))
      CFSG.KD.OrdHN.ONE = true ∧
    Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KD.HNPt.R 35) (CFSG.KC.LL.HN.mm (CFSG.KD.HNPt.R 35)
      (CFSG.KD.HNPt.R 35))) CFSG.KD.OrdHN.ONE = true := by
  refine ⟨?_, ?_⟩ <;> quickRfl

theorem pl2 : allN 8799 (fun k => Nat.blt (fldW PL2 (Nat.mul 21 k) 21)
      (fldW PL2 (Nat.mul 21 (Nat.add k 1)) 21)) = true ∧
    allN 6 (fun j => Nat.beq (fldW (IM j) 0 21) 0) = true ∧
    allN 8799 (fun k => Bool.not (allN 6 (fun j => Nat.beq (fldW (IM j) (Nat.mul 21 (Nat.add k 1)) 21)
      (fldW PL2 (Nat.mul 21 (Nat.add k 1)) 21)))) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> quickRfl

theorem neg_w : Bool.not (Nat.beq (wordC CFSG.KD.HNPt.R (ecF 2)) (EL 1)) = true := by quickRfl
theorem neg_t : Bool.not (Nat.beq (trM (EL 1)) (TT 2)) = true := by quickRfl
theorem neg_comm : Bool.not (Nat.beq (CFSG.KC.LL.HN.mm (EL 21) (EL 22))
    (CFSG.KC.LL.HN.mm (EL 22) (EL 21)) && Nat.beq (CFSG.KC.LL.HN.mm (CFSG.KD.HNPt.R 34)
    (CFSG.KD.HNPt.R 35)) (CFSG.KC.LL.HN.mm (CFSG.KD.HNPt.R 35) (CFSG.KD.HNPt.R 34))) = true := by
  quickRfl
theorem neg_pl2 : Bool.not (allN 6 (fun j => Nat.beq (fldW (IM j) 21 21) 0)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2094

end
