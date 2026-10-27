
module

public import Certificates.Kernel.Sporadic.L2C.G1Base

public import Certificates.Kernel.Sporadic.L2C.Defs
public import Certificates.Kernel.Sporadic.L2.G4
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverDefsBase

public section

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoCover CFSG.Sporadic.SuzRecog.LevelTwoCoverData
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ElimCert
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (sB band bif_true nbeq nblt nble nblt_f nble_f allN_get
  hexE hexTable_at nbr_get nbr_size nbr_high)

attribute [local irreducible] volt shift nbr

theorem coverBaseOK_true (H : BaseH) : coverBaseOK = true := by
  unfold coverBaseOK baseOf
  rw [allLt_iff]
  intro x hx
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨nbr_size hx, allLt_iff.2 fun k hk => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := base_at H hx hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.any_eq_true, List.mem_range, beq_iff_eq, nbr_get hx hk]
  refine ⟨⟨⟨c1, c2⟩, allLt_iff.2 fun j hj => ?_⟩, ?_⟩
  · rw [nbr_get hx (by omega), bne_iff_ne]
    exact c3 j hj
  · by_cases hy : 2835 ≤ nbK x k
    · exact Or.inl hy
    · obtain ⟨j, hj, e1, e2⟩ := c4 (by omega)
      refine Or.inr ⟨j, hj, ?_, ?_⟩
      · rw [nbr_get (by omega) hj]
        exact e1
      · rw [volt_get hx hk, volt_get (by omega) hj]
        exact e2

end CertificateChecks.KernelSpor.L2CG

end
