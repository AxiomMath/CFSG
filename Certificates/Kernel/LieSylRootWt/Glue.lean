module

public import Certificates.Data.LieSylRootWt
public import Certificates.Kernel.LieSylRootWt.Checks
public import CFSG.Certificates.Kernel.LieSylRootWtSound
public import Mathlib.Tactic.Ring

public section

namespace CertificateChecks.KernelLieSylRootWt

open Certificates.Data.LieSylRootWt Certificates.Data.LieSylRootWtK CFSG.KD.LieSylRootWt

theorem d4_holds : rootWeightStabCheck .D4 11 24 = true := by
  have h := stabCheck_eq Ty.D4.roots (length_roots .D4) MK_D4
    (Nat.eq_of_beq_eq_true ch617001mD4) 24
  rw [beq_iff_eq.mp ch617001tD4, beq_iff_eq.mp ch617001lD4] at h
  exact h.trans ch617001D4

theorem f4_holds : rootWeightStabCheck .F4 11 24 = true := by
  have h := stabCheck_eq Ty.F4.roots (length_roots .F4) MK_F4
    (Nat.eq_of_beq_eq_true ch617001mF4) 24
  rw [beq_iff_eq.mp ch617001tF4, beq_iff_eq.mp ch617001lF4] at h
  exact h.trans ch617001F4

end CertificateChecks.KernelLieSylRootWt

end
