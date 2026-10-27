module

public import CFSG.Monster.GMS.Griess13.ChecksOrbitTab

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelG13

open CFSG.Monster.GMS.Griess13.Co1Data
open scoped Matrix

theorem codeOf_lt : ∀ v : Fin 6 → ZMod 3, codeOf v < 729 := by decide +kernel

theorem vecOfCode_codeOf : ∀ v : Fin 6 → ZMod 3, vecOfCode (codeOf v) = v := by decide +kernel

theorem codeOf_pos : ∀ v : Fin 6 → ZMod 3, v ≠ 0 → 0 < codeOf v := by decide +kernel

theorem vecOfCode_ne_zero : ∀ c < 729, 0 < c → vecOfCode c ≠ 0 := by decide +kernel

theorem vecOfCode_stepS :
    ∀ s : Fin 2, ∀ c < 729, vecOfCode (stepS s.val c) = actN s *ᵥ vecOfCode c := by
  decide +kernel

theorem orbCheckR_true : orbCheckR = true := by decide +kernel

theorem orbitClassR_repw : ∀ k : Fin 12, orbitClassR (repw k) = 1 := by decide +kernel

theorem orbitClassR_w1 : orbitClassR w1 = 1 := by decide +kernel

theorem orbitClassR_wB : orbitClassR wB = 2 := by decide +kernel

theorem orbitClassR_wC : orbitClassR wC = 3 := by decide +kernel

theorem orbitClassR_neg : ∀ w : Fin 6 → ZMod 3, orbitClassR (-w) = orbitClassR w := by decide +kernel

theorem orbitClassR_one_spec :
    ∀ w : Fin 6 → ZMod 3, w ≠ 0 → orbitClassR w = 1 →
      ∃ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ w = c • repw k := by
  decide +kernel

theorem card_orbitClassR_one :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 1).card = 24 := by
  decide +kernel

theorem card_orbitClassR_two :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 2).card = 264 := by
  decide +kernel

theorem card_orbitClassR_three :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 3).card = 440 := by
  decide +kernel

theorem card_orbitIndexR_zero :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 0).card = 24 := by
  decide +kernel

theorem card_orbitIndexR_one :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 1).card = 264 := by
  decide +kernel

theorem card_orbitIndexR_two :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 2).card = 440 := by
  decide +kernel

theorem repw_ne_zero : ∀ k : Fin 12, repw k ≠ 0 := by decide +kernel

end CertificateChecks.KernelG13

end
