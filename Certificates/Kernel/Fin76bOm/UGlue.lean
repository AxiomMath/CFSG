module

public import Certificates.Kernel.Fin76bOm.UChecks
public import CFSG.Certificates.Kernel.Fin76bOm.UTwinSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCheck

public section

namespace CertificateChecks.KernelC24608

open CFSG.KC.Fin76bU CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16

theorem tblU_of {P : Nat} {M : Nat → Nat → Nat}
    (h : ((List.range 32).all fun a => (List.range 32).all fun b => mU P a b == M a b) = true) :
    ∀ a < 32, ∀ b < 32, mU P a b = M a b := by
  intro a ha b hb
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb

theorem j2U_spec : UTableSpec mulE0 eT :=
  UTableSpec_congr (fun a _ b _ => mU_lt J2U.P a b) (tblU_of j2U_tbl) (uChkU_spec j2U_chk)

theorem j3U_spec : UTableSpec mulEJ3 21 :=
  UTableSpec_congr (fun a _ b _ => mU_lt J3U.P a b) (tblU_of j3U_tbl) (uChkU_spec j3U_chk)

end CertificateChecks.KernelC24608

end
