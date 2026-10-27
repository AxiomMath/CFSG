module

public import Certificates.Kernel.Misc.RuSq.Chain
public import Certificates.Kernel.Misc.TextBlocks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.RuSqT CFSG.Sporadic.RuSchreier.ru4060Text

namespace CertificateChecks.KernelMisc.RuSq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelMisc.TextBlocks

theorem asciiB39 : asciiBlocks 39 (3 * 4060 + 1) RuSqT.chars = true := by
  quickRfl

theorem asciiOK : asciiK (RuSqT.chars.take (39 * (3 * 4060 + 1))) = true :=
  asciiBlocks_spec asciiB39

@[expose] noncomputable def lineOK (j : Nat) : Bool :=
  lineK 3 4060 12 (RuSqS.S j) (RuSqT.chars.drop ((33 + j) * (3 * 4060 + 1)))

theorem line0 : lineOK 0 = true := by quickRfl
theorem line1 : lineOK 1 = true := by quickRfl
theorem line2 : lineOK 2 = true := by quickRfl
theorem line3 : lineOK 3 = true := by quickRfl
theorem line4 : lineOK 4 = true := by quickRfl
theorem line5 : lineOK 5 = true := by quickRfl

theorem lineAll : ∀ j < 6, lineOK j = true := by
  intro j hj
  interval_cases j
  exacts [line0, line1, line2, line3, line4, line5]


theorem row_eq {j : Nat} (hj : j < 6) : ruArr4060 (33 + j) = unpack 4060 12 (RuSqS.S j) := by
  have ha : asciiK (RuSqT.chars.take ((33 + j + 1) * (3 * 4060 + 1))) = true :=
    asciiK_take (by omega) asciiOK
  have hk : lineK 3 4060 12 (RuSqS.S j) (RuSqT.chars.drop ((33 + j) * (3 * 4060 + 1))) = true :=
    lineAll j hj
  have hl := lineK_sound ha hk
  unfold ruArr4060 ruHexRow ruBytes4060 ruHexAt
  rw [RuSqT.eq]
  apply Array.ext
  · simp [CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact hl i (by simpa using h1)

theorem baseOK : allN 2 (fun t => Nat.beq (ruBaseArr 4060 ruS4060ChainBase)[t]!
    (pg 12 (mask 12) RuSqS.BP t)) = true := by
  quickRfl

theorem permS : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuSqS.S j) (RuSqS.SI j)) =
    true := by
  quickRfl

theorem bindsSq : Binds 4060 12 RuSqS.S 6 2 RuSqS.BP (ruField4060 4)
    (ruBaseArr 4060 ruS4060ChainBase) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [ruField4060, ruLines4060], fun j hj => ?_,
    by simp [ruBaseArr, ruS4060ChainBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩
  rw [ruField4060, getElem!_pos _ j (by simpa [ruLines4060] using hj), Array.getElem_ofFn]
  exact row_eq hj

end CertificateChecks.KernelMisc.RuSq

end
