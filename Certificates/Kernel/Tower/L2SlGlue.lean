module

public import Certificates.Kernel.Tower.E14Glue
public import Certificates.Kernel.Tower.E14XChecks
public import CFSG.Certificates.Kernel.Tower.Search14Sound

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

variable {X : Type*} [Group X] {dec : Nat → X}

theorem slE_l2_of {D0 : Nat → Nat} {j a g nl c1 c2 n1 n2 : Nat}
    (M : IsModel (⊤ : Subgroup X) 16384 (slEm a g) dec)
    (ho : e14Ord D0 a g = true) (hl : e14Lab D0 a g nl = true) (hh : e14H D0 a g = true)
    (hc : e14Cm D0 a g c1 c2 = true) (h12 : e14L12 D0 a g c1 c2 n1 n2 = true)
    (h3 : allB n2 (e14L3 D0 a g n1) = true) (hpc : e14Pc D0 a g nl = true)
    (hchi : e14Chi D0 j a g = true) : L2Facts X (dec 128) := by
  simp only [e14Lab, e14H, e14Cm, e14L12, Bool.and_eq_true] at hl hh hc h12
  have hT : treeB 16384 4 (slEm a g) (D0 5) (D0 7) = true := hh.1.2
  have hx0 : l16 (D0 5) 0 < 16384 := treeB_gen hT (by norm_num)
  have hno : ∀ β : MulAut X, β (dec (l16 (D0 5) 0)) ≠ dec 128 := fun β =>
    e14_empty (W2 := fun r1 => D0 (Nat.add 17 r1))
      (SP := fun r2 => D0 (Nat.add 17 (Nat.add n1 r2))) rfl M hT ho hl.1 hl.2 hh.1.1 hh.2
      hc.1 hc.2 h12.1 h12.2 h3 β
  obtain ⟨hnt, hnx⟩ := not_mem_bitQ M hT hchi (by norm_num) hx0
  exact l2Facts_of_parts (bitQ M hT hchi) (bitQ_normal M hT hchi)
    (bitQ_index M hT hchi (by norm_num)) hnt hnx
    (pcB_sound M rfl hT (by norm_num) hx0 ho hl.1 hl.2 hpc) hno

theorem slE0_l2 (M : IsModel (⊤ : Subgroup X) 16384 (slEm 0 132) dec) : L2Facts X (dec 128) :=
  slE_l2_of M ch36409_e0_ord ch36409_e0_lab ch36409_e0_h ch36409_e0_cm ch36409_e0_l12
    (allB_two ch36409_e0_l30 ch36409_e0_l31) ch36409_e0_pc ch36409_e0_chi

theorem slE1_l2 (M : IsModel (⊤ : Subgroup X) 16384 (slEm 2 132) dec) : L2Facts X (dec 128) :=
  slE_l2_of M ch36409_e1_ord ch36409_e1_lab ch36409_e1_h ch36409_e1_cm ch36409_e1_l12
    (allB_two ch36409_e1_l30 ch36409_e1_l31) ch36409_e1_pc ch36409_e1_chi

theorem slE2_l2 (M : IsModel (⊤ : Subgroup X) 16384 (slEm 9 0) dec) : L2Facts X (dec 128) :=
  slE_l2_of M ch36409_e2_ord ch36409_e2_lab ch36409_e2_h ch36409_e2_cm ch36409_e2_l12
    (allB_two ch36409_e2_l30 ch36409_e2_l31) ch36409_e2_pc ch36409_e2_chi

theorem slE3_l2 (M : IsModel (⊤ : Subgroup X) 16384 (slEm 11 0) dec) : L2Facts X (dec 128) :=
  slE_l2_of M ch36409_e3_ord ch36409_e3_lab ch36409_e3_h ch36409_e3_cm ch36409_e3_l12
    (allB_two ch36409_e3_l30 ch36409_e3_l31) ch36409_e3_pc ch36409_e3_chi

end Certificates.KernelTower
