module

public import Certificates.Kernel.OmegaEight.SB3872L2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem fStates_eq {k : ℕ} (hstep : ∀ i < 7, fStep k i (fL k i) = fL k (i + 1))
    (h0 : fL k 0 = [[]]) : ∀ i ≤ 7, sAutData.fStates sMul sInv k i = fL k i := by
  intro i
  induction i with
  | zero => intro _; rw [h0]; rfl
  | succ i ih =>
    intro hi
    rw [← hstep i (by omega), ← ih (by omega)]
    simp only [AutData.fStates, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, fStep]

set_option maxHeartbeats 0 in
theorem leaves_check : sLeavesCheck = true := by
  unfold sLeavesCheck
  refine List.all_eq_true.2 fun k hk => ?_
  have hk : k < 8 := List.mem_range.1 hk
  have hstep : ∀ i < 7, fStep k i (fL k i) = fL k (i + 1) := by
    interval_cases k
    exacts [fStep_0, fStep_1, fStep_2, fStep_3, fStep_4, fStep_5, fStep_6, fStep_7]
  have h0 : fL k 0 = [[]] := by interval_cases k <;> decide +kernel
  rw [AutData.fSearch, (by rfl : sAutData.q = 7), fStates_eq hstep h0 7 le_rfl, beq_iff_eq]
  interval_cases k <;> decide +kernel

end CertificateChecks.KernelO8.SB3872

end
