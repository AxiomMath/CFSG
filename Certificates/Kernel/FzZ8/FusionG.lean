module

public import Certificates.Kernel.FzZ8.Fusion3
public import Certificates.Kernel.FzZ8.Fusion7
public import CFSG.Certificates.Kernel.FzZ8.Par

public section

namespace CFSG.KC.FzZ8

open Certificates.FzR10A CFSG.OddStandard.SmallF3.FritzII

theorem pk_reps : pkM ⟨5, 0, 0, 5⟩ = 2565 ∧ pkM ⟨3, 0, 0, 3⟩ = 1539 ∧ pkM ⟨7, 0, 0, 7⟩ = 3591 ∧
    pkM ⟨0, 1, 1, 0⟩ = 72 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem fusion_r3 : ¬ ∃ θ : ℕ → Prop, FzRules (parOfA ⟨5, 0, 0, 5⟩ ⟨3, 0, 0, 3⟩ ⟨0, 1, 1, 0⟩) θ := by
  have hP := fuParA (t := ⟨5, 0, 0, 5⟩) (s := ⟨3, 0, 0, 3⟩) (l := ⟨0, 1, 1, 0⟩)
    (by unfold FzR10AMatLt; decide) (by unfold FzR10AMatLt; decide)
    (by unfold FzR10AMatLt; decide)
  rw [pk_reps.1, pk_reps.2.1, pk_reps.2.2.2] at hP
  exact refuteG hP R3.ch441791_r3_forest R3.ch441791_r3_dead R3.ch441791_r3_iw
    R3.ch441791_r3_xt R3.ch441791_r3_ts R3.ch441791_r3_tk
    (leaves8_of R3.ch441791_r3_leaves0 R3.ch441791_r3_leaves4)

theorem fusion_r7 : ¬ ∃ θ : ℕ → Prop, FzRules (parOfA ⟨5, 0, 0, 5⟩ ⟨7, 0, 0, 7⟩ ⟨0, 1, 1, 0⟩) θ := by
  have hP := fuParA (t := ⟨5, 0, 0, 5⟩) (s := ⟨7, 0, 0, 7⟩) (l := ⟨0, 1, 1, 0⟩)
    (by unfold FzR10AMatLt; decide) (by unfold FzR10AMatLt; decide)
    (by unfold FzR10AMatLt; decide)
  rw [pk_reps.1, pk_reps.2.2.1, pk_reps.2.2.2] at hP
  exact refuteG hP R7.ch441791_r7_forest R7.ch441791_r7_dead R7.ch441791_r7_iw
    R7.ch441791_r7_xt R7.ch441791_r7_ts R7.ch441791_r7_tk
    (leaves8_of R7.ch441791_r7_leaves0 R7.ch441791_r7_leaves4)

end CFSG.KC.FzZ8
