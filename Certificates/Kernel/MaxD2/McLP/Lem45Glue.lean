module

public import Certificates.Kernel.MaxD2.McLP.Glue
public import Certificates.Kernel.MaxD2.McLP.Lem45Checks
public import CFSG.Certificates.Kernel.MaxD2.Lem45

public section

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem mcl_lem45 :
    McLLem45.check Certificates.MaxD2Heis.mclFiveDataP McLLem45.wordW McLLem45.tree = true := by
  have hne : Nat.beq (wcK 275 9 (RE.G 0) (WL 0) 1) (wcK 275 9 (RE.G 0) (WL 0) 0) = false := by
    have h := l45_ne
    revert h
    cases Nat.beq (wcK 275 9 (RE.G 0) (WL 0) 1) (wcK 275 9 (RE.G 0) (WL 0) 0)
    · intro _
      rfl
    · intro h
      exact absurd h (by decide)
  exact lem45_check_of (W := WL 0) (nz := 5) (m := 120) (IX := r32 IX) (CV := r32 CV) hypsH l45_w
    l45_wcn l45_u5 l45_ww (fun k hk l hl => (PK.allN_iff.1 ((PK.allN_iff.1 l45_wc) k hk)) l hl)
    hne (Nat.blt_eq.mp l45_i0) (Nat.eq_of_beq_eq_true l45_i0') l45_tree rfl rfl
    (fun i hi => (PK.allN_iff.1 l45_cov) i hi)

end CertificateChecks.KernelMaxD2.McLP
