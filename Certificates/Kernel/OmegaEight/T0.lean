module

public import CFSG.Certificates.Kernel.O8T0Sound
public import Certificates.Kernel.OmegaEight.Chain
public import Certificates.Kernel.OmegaEight.T0Checks
import Certificates.Kernel.OmegaEight.Forms
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainShapeBData

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.Chain CFSG.KLie.CT CFSG.KC.Loop

theorem bindGP : ∀ s < 6, genRows .plus s = decR (mat GPlus s) := by
  intro s hs
  interval_cases s <;> rfl

theorem bindCP : ∀ s < 6, c0Rows .plus s = decR (mat CPlus s) := by
  intro s hs
  interval_cases s <;> rfl

set_option maxRecDepth 20000 in
theorem bindW : s0Words.toList = S0W := rfl

theorem liftTab_eq : liftTab = liftTabG (genRows .plus) (c0Rows .plus) s0Words := by
  unfold liftTab liftTabG
  rw [prod4_eq]

theorem wordsCheck_eq : wordsCheck = wordsCheckG (genRows .plus) (s0List .plus) s0Words := by
  unfold wordsCheck wordsCheckG
  rw [wordRows_eq]
  rfl

theorem t0Check_eq :
    t0Check = t0CheckG (s0List .plus) (liftTabG (genRows .plus) (c0Rows .plus) s0Words) := by
  unfold t0Check
  rw [liftTab_eq]
  rfl

theorem commCheck_eq :
    commCheck = commCheckG (s0List .plus) (liftTabG (genRows .plus) (c0Rows .plus) s0Words) := by
  unfold commCheck
  rw [liftTab_eq]
  rfl

theorem cert3494 :
    (wordsCheck = true) ∧ (uIdxCheck = true) ∧ (e0Check = true) ∧ (t0Check = true) := by
  rw [wordsCheck_eq, t0Check_eq]
  exact ⟨words_sound bindLP bindGP bindW kWords, uIdx_sound bindLP bindUP kUIdx,
    e0_sound bindLP kE0, t0_sound bindLP bindGP bindCP bindW kWords kDistP kMtP kT0⟩

theorem cert3495 : commCheck = true := by
  rw [commCheck_eq]
  exact comm_sound bindLP bindGP bindCP bindW kWords kDistP kMtP kComm

end CertificateChecks.KernelO8

end
