
module

public import Certificates.Kernel.L34Cov.LiftNormChecks
public import Certificates.Kernel.L34Cov.Field22234
public import Certificates.Kernel.LocalComp.L34Para.Final
public import Certificates.Kernel.L34W.Glue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W CFSG.KC.L34KSnd
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W

theorem gT4 : r₂T = unpack 42 6 (GT 4) ∧ Cn (GT 4) := by
  obtain ⟨e, c⟩ := gensG 4 (by norm_num)
  exact ⟨e, c⟩

theorem gT5 : r₃T = unpack 42 6 (GT 5) ∧ Cn (GT 5) := by
  obtain ⟨e, c⟩ := gensG 5 (by norm_num)
  exact ⟨e, c⟩

theorem conj_unpack {g x : ℕ} (hg : Cn g) (hx : Cn x) :
    conjTab 42 (unpack 42 6 g) (unpack 42 6 g) (unpack 42 6 x) = unpack 42 6 (cjK g x) := by
  rw [conjTab, comp_unpack' hg hx, comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp hg hx) hg]
  rfl

theorem liftNormOK_k : liftNormOK = true := by
  unfold liftNormOK
  dsimp only
  rw [rT.1, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [CFSG.PSL3Four.Native.allBelow, List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    obtain ⟨hc, e⟩ := tgK_eq gensG k
    obtain ⟨h2, h3⟩ := andB_iff.1 (allN' ch22212n_k k hk)
    rw [Bool.and_eq_true, e, gT4.1, gT5.1, conj_unpack gT4.2 hc, conj_unpack gT5.2 hc]
    exact ⟨found_of h2, found_of h3⟩
  · rw [gT4.1, gT5.1, comp_unpack' gT4.2 gT5.2, comp_unpack' gT5.2 gT4.2,
      Nat.eq_of_beq_eq_true ch22212n_c]
    exact beq_self_eq_true _

theorem alphaG_eq (w : List (Fin 2 × Bool)) : alphaG w = substWord (autWs uAG uBG) w := rfl

theorem alphaU_eq (w : List (Fin 2 × Bool)) : alphaU w = substWord (autWs uAU uBU) w := rfl

theorem facts22212 :
    (∀ s ∈ liftSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    liftNormOK = true := by
  refine ⟨fun s hs => ?_, liftNormOK_k⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rw [cv_zword]
  simp only [liftSpecs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · dsimp only
    rw [show alphaF liftW0 = substWord (autWs uAF uBF) liftW0 from rfl]
    exact (lift_eq ch22212l_F List.mem_cons_self).trans (by norm_num)
  · dsimp only
    rw [alphaG_eq]
    exact (lift_eq ch22212l_G List.mem_cons_self).trans (by norm_num)
  · dsimp only
    rw [alphaU_eq]
    exact (lift_eq ch22212l_U List.mem_cons_self).trans (by norm_num)
  · exact cv_eq_of_cvId ch22212l_sq

end CertificateChecks.KernelL34Cov

end
