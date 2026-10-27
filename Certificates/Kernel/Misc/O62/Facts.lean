module

public import Certificates.Kernel.Misc.O62.Kernel
public import CFSG.Certificates.Kernel.Misc.O62Sound
import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KD.Misc.O62

open CFSG.KC.Misc.O62 CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Check

theorem rxPAll : ∀ i < 43, rankX IPP i = true := (CFSG.KC.Misc.Clos.allN_iff _ _).1 rxP
theorem rxMAll : ∀ i < 43, rankX IPM i = true := (CFSG.KC.Misc.Clos.allN_iff _ _).1 rxM
theorem wxPAll : ∀ i < 43, wcX 0 IQP certsPlus EPP i = true :=
  (CFSG.KC.Misc.Clos.allN_iff _ _).1 wxP
theorem wxMAll : ∀ i < 43, wcX 1 IQM certsMinus EPM i = true :=
  (CFSG.KC.Misc.Clos.allN_iff _ _).1 wxM

theorem facts : (checkSylow false = true) ∧ (checkSylow true = true) ∧ (checkRank false = true) ∧
    (checkRank true = true) ∧ (checkWC false = true) ∧ (checkWC true = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [checkSylow_eq]
    exact sylowK_sound (minus := false) sylowP
  · rw [checkSylow_eq]
    exact sylowK_sound (minus := true) sylowM
  · rw [checkRank_eq]
    exact rankK_sound sylowP rankPreP (Nat.eq_of_beq_eq_true cntPP) rxPAll
  · rw [checkRank_eq]
    exact rankK_sound sylowM rankPreM (Nat.eq_of_beq_eq_true cntPM) rxMAll
  · rw [checkWC_eq]
    exact wcK_sound (minus := false) invParP certP (Nat.eq_of_beq_eq_true cntQP) wxPAll
  · rw [checkWC_eq]
    exact wcK_sound (minus := true) invParM certM (Nat.eq_of_beq_eq_true cntQM) wxMAll

end CFSG.KD.Misc.O62

end
