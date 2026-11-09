module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5120

open CFSG.GH74.KGroups.L33

theorem kE9_at {n : Nat} [Small n] (L : List (CV n)) (τ : CV n) : e9atC (centL L τ) =
    e9atC ((L.filter fun g => powOneC g 3).filter fun g => eq22C g τ τ g) := by
  have h1 : ((L.filter fun g => powOneC g 3).filter fun g => eq22C g τ τ g) =
      (centL L τ).filter fun g => powOneC g 3 := by
    unfold centL
    rw [List.filter_filter, List.filter_filter]
    congr 1
    funext g
    exact Bool.and_comm _ _
  rw [h1]
  generalize centL L τ = C
  simp only [e9atC, List.all_filter]
  refine congrArg (List.all C) (funext fun X => ?_)
  cases powOneC X 3
  · simp
  · refine congrArg (List.all C) (funext fun Y => ?_)
    cases powOneC Y 3 <;> simp

noncomputable def kE9B (j : Nat) : Bool :=
  (((elemsC QA).drop (j * 2808)).take 2808).all fun τ =>
    bif powOneC τ 2 && !decide (τ = 1) then
      e9atC (((elemsC QA).filter fun g => powOneC g 3).filter fun g => eq22C g τ τ g) else true

#kc_each kE9B 0 4

theorem kE9 : e9freeC (elemsC QA) = true := by
  have hb : ∀ j < 4, kE9B j = true := by
    intro j hj
    interval_cases j
    exacts [kE9B0, kE9B1, kE9B2, kE9B3]
  unfold e9freeC
  simp only [kE9_at]
  exact PkEnum.all_of_chunks _ _ 2808 4 (by decide +kernel) hb

theorem kE9_neg : ((elemsC QA).all fun τ => bif powOneC τ 2 && !decide (τ = 1) then
    (centL (elemsC QA) τ).all fun X => !powOneC X 3 || decide (X = 1) else true) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5120
