
module

public import Certificates.Kernel.OmegaEight.SB3873GH
public import CFSG.Certificates.Kernel.O8.SBClsSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBCenL CFSG.KC.SBCenU CFSG.KC.SBCls

@[expose] noncomputable def clsAtT (k m z : ℕ) (r : ℕ × ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    clsChk (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
      (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens 131072 r

theorem clsAtF_of_T {k m z : ℕ} {r : ℕ × ℕ} (h : clsAtT k m z r = true) :
    clsAtF k m z r = true := by
  unfold clsAtT at h
  unfold clsAtF
  simp only [cen_strictB] at h ⊢
  exact clsChk_imp _ _ _ h

theorem all_clsAt_of_T {k m z : ℕ} {L : List (ℕ × ℕ)} (h : L.all (clsAtT k m z) = true) :
    L.all (clsAt k m z) = true := by
  rw [← clsAtF_eq]
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => clsAtF_of_T (h r hr)

macro "t1cenS " Q:term ", " B:term : tactic => `(tactic| (
  refine t1KillC_of_cen (Q := $Q) (B := $B) ?_ ?_ ?_ ?_
  · refine ⟨conjOK_of_hom (by decide +kernel) (by decide), by decide +kernel, by decide +kernel, ?_,
      ?_, by decide, ?_⟩
    · simp only [chiWOK, chiS_get]
      decide +kernel
    · simp only [chiLOK, chiS_get]
      decide +kernel
    · rw [chiS_get]
      decide +kernel
  · refine ⟨fun s hs => ?_, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩
    refine all_clsAt_of_T ?_
    interval_cases s <;> decide +kernel
  · refine CenB_of_F (CenBF_of_L (CenBL_of_U (by decide) ⟨fun s hs => ?_, fun t ht => ?_⟩))
    · interval_cases s <;> decide +kernel
    · interval_cases t <;> decide +kernel
  · refine CenK_of_F ?_
    unfold CenKF
    simp only [sMarked, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩))

end CertificateChecks.KernelO8.SB3873

end
