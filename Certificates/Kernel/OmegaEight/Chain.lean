module

public import CFSG.Certificates.Kernel.O8ChainSound
public import Certificates.Kernel.OmegaEight.S0Checks

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.Chain CFSG.KLie.CT

theorem bindLP : S0Bind (s0List .plus) LPlus := ⟨rfl, fun i hi => by interval_cases i <;> rfl⟩
theorem bindLM : S0Bind (s0List .minus) LMinus := ⟨rfl, fun i hi => by interval_cases i <;> rfl⟩

theorem bindUP : ∀ k < 6, uRows .plus k = decR (mat UPlus k) := by
  intro k hk
  interval_cases k <;> rfl

theorem bindUM : ∀ k < 6, uRows .minus k = decR (mat UMinus k) := by
  intro k hk
  interval_cases k <;> rfl

theorem bindTP : ∀ i < 64, (s0Tree .plus).getD i (0, 0) = (fget TRPlus i 9 % 8, fget TRPlus i 9 / 8) := by
  intro i hi
  interval_cases i <;> rfl

theorem bindTM :
    ∀ i < 64, (s0Tree .minus).getD i (0, 0) = (fget TRMinus i 9 % 8, fget TRMinus i 9 / 8) := by
  intro i hi
  interval_cases i <;> rfl

set_option maxRecDepth 20000 in
theorem bindAP : abelMasks .plus = (List.range NPlus).map fun k => fget AMPlus k 64 := rfl

set_option maxRecDepth 20000 in
theorem bindAM : abelMasks .minus = (List.range NMinus).map fun k => fget AMMinus k 64 := rfl

theorem s0Check_eq (ε : Eps) : s0Check ε = s0CheckG (s0List ε) (uRows ε) (s0Tree ε) := rfl

theorem abelCheck_eq (ε : Eps) : abelCheck ε = abelCheckG (s0List ε) (abelMasks ε) := rfl

theorem cert3492 : (s0Check .plus = true) ∧ (s0Check .minus = true)
    ∧ (abelCheck .plus = true) ∧ (abelCheck .minus = true) := by
  rw [s0Check_eq, s0Check_eq, abelCheck_eq, abelCheck_eq]
  exact ⟨s0_sound bindLP bindUP bindTP kMtP kS0P, s0_sound bindLM bindUM bindTM kMtM kS0M,
    abel_sound bindLP bindAP (by decide +kernel) kDistP kMtP kAbelP,
    abel_sound bindLM bindAM (by decide +kernel) kDistM kMtM kAbelM⟩

end CertificateChecks.KernelO8

end
