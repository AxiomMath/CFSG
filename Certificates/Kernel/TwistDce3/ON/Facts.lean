module

public import Certificates.Kernel.TwistDce3.ON.Walk

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce2 CFSG.KC.TwDce3 CFSG.Certificates.TwDce CFSG.Certificates.CosetEnumeration

theorem hgen_lt : ∀ c < 6, onHGen c = 0 ∨ onHGen c = 1 ∨ onHGen c = 2 := by decide

theorem inv_eq : ∀ c < 12, ivL INVM c = if c < 6 then (if c % 2 = 0 then c + 1 else c - 1) else c := by
  decide +kernel

theorem onHGen_congr {d e : ℕ} (h : d / 2 = e / 2) : onHGen d = onHGen e := by
  simp only [onHGen, h]

theorem hinv : ∀ c < 12, ivL INVM c < 12 ∧ onX (ivL INVM c) = (onX c)⁻¹ := by
  intro c hc
  refine ⟨by rw [inv_eq c hc]; split_ifs <;> omega, ?_⟩
  rw [inv_eq c hc]
  by_cases h6 : c < 6
  · rw [if_pos h6]
    by_cases h : c % 2 = 0
    · rw [if_pos h]
      simp only [onX, if_pos h6, if_pos (show c + 1 < 6 by omega), if_pos h,
        if_neg (show ¬ (c + 1) % 2 = 0 by omega), onHGen_congr (show (c + 1) / 2 = c / 2 by omega)]
    · rw [if_neg h]
      simp only [onX, if_pos h6, if_pos (show c - 1 < 6 by omega), if_neg h,
        if_pos (show (c - 1) % 2 = 0 by omega), inv_inv,
        onHGen_congr (show (c - 1) / 2 = c / 2 by omega)]
  · rw [if_neg h6]
    simp [onX, h6]

theorem nt_eq : NT = 4 := by decide +kernel

theorem psf_eq : PSF = idMap := by decide +kernel

theorem psb_eq : PSB = idMap := by decide +kernel

set_option maxRecDepth 100000 in
theorem hlenR : ∀ r < 4625, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧
    CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16 := by
  decide +kernel

end CFSG.KD.ONDce3

end
