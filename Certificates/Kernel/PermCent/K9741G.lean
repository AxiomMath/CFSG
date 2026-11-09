module

public import Certificates.Data.Kernel.PermCent.GoodC
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K9741G

open CFSG.Certificates.Kernel.PkCV.Good CFSG.GH74.KGroups.L33 CFSG.ClassicalInvolution.Q3.TA3.Check

@[expose] def l33PickGaps {α : Type*} : List α → List Nat → List α
  | _, [] => []
  | l, d :: ds => match l.drop d with
    | [] => []
    | a :: r => a :: l33PickGaps r ds

theorem mem_l33PickGaps {α : Type*} {l : List α} {ds : List Nat} {a : α}
    (h : a ∈ l33PickGaps l ds) : a ∈ l := by
  induction ds generalizing l with
  | nil => simp [l33PickGaps] at h
  | cons d ds ih =>
    rw [l33PickGaps] at h
    split at h
    · simp at h
    · rename_i b r hr
      have hsub : b :: r ⊆ l := hr ▸ List.drop_subset d l
      rcases List.mem_cons.1 h with rfl | h
      · exact hsub List.mem_cons_self
      · exact hsub (List.mem_cons_of_mem _ (ih h))

@[expose] noncomputable def l33T0 : CV 26 := (elemsC QP).getD 1 1

@[expose] def l33ConjD : List Nat :=
  [0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 327, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    327, 3, 3, 3, 3, 3, 3, 3, 3, 39, 3, 3, 3, 3, 3, 3, 3, 3, 291, 3, 3, 3, 3, 3, 3, 3, 3, 471, 3, 3,
    3, 3, 3, 3, 3, 3, 363, 3, 3, 3, 3, 3, 3, 3, 3, 435, 3, 3, 3, 3, 3, 3, 3, 3]

@[expose] noncomputable def l33ConjT : List (CV 26) := l33PickGaps (elemsC QP) l33ConjD

@[expose] noncomputable def l33ConjJ : List (CV 26) := l33ConjT.map fun g => g * l33T0 * g⁻¹

theorem k9741_conj : ((elemsC QP).filter fun t => powOneC t 2 && !decide (t = 1)).all
    (fun t => decide (t ∈ l33ConjJ)) = true := by decide +kernel

theorem k9741_cent : (noOddC 100 (centC (elemsC QP) l33T0) &&
    pairsB l33T0 (centC (elemsC QP) l33T0)) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K9741G
