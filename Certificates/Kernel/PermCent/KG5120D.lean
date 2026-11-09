module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpConjSound
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5120

open CFSG.GH74.KGroups.L33 CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

theorem kAll_filter {α : Type*} (L : List α) (p g : α → Bool) :
    (L.all fun x => bif p x then g x else true) = (L.filter p).all g := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, ih]
    cases h : p a <;> simp [List.filter, h]

theorem kAllPerm {α : Type*} {l₁ l₂ : List α} (h : l₁.Perm l₂) (p : α → Bool) :
    l₁.all p = l₂.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall_congr' fun x => imp_congr_left h.mem_iff

section Conj

variable {n : Nat} [Small n]

theorem kCentPerm (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {g : CV n} (hg : g ∈ elemsC Q)
    (x : CV n) :
    (centL (elemsC Q) (g * x * g⁻¹)).Perm ((centL (elemsC Q) x).map (MulAut.conj g)) := by
  have hg' : g⁻¹ ∈ elemsC Q := by
    rw [mem_elemsC Q hQ] at hg ⊢
    rw [← ev_inv']
    exact Q.originalSubgroup.inv_mem hg
  have hnd := nodup_elemsC Q hQ
  refine (List.perm_ext_iff_of_nodup (hnd.filter _)
    ((hnd.filter _).map (MulAut.conj g).injective)).2 fun y => ?_
  simp only [centL, List.mem_filter, List.mem_map, eq22C_eq, decide_eq_true_eq, MulAut.conj_apply]
  constructor
  · rintro ⟨hy, hc⟩
    refine ⟨g⁻¹ * y * g, ⟨by simpa using conj_mem_elemsC Q hQ hg' hy, ?_⟩, by group⟩
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hc]
      _ = x * (g⁻¹ * y * g) := by group
  · rintro ⟨z, ⟨hz, hc⟩, rfl⟩
    refine ⟨conj_mem_elemsC Q hQ hg hz, ?_⟩
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group

theorem kCent3Map (φ : CV n ≃* CV n) (x : CV n) (C : List (CV n)) :
    cent3atC (φ x) (C.map φ) = cent3atC x C := by
  unfold cent3atC
  have hm : ∀ (y : CV n) (L : List (CV n)), decide (φ y ∈ L.map φ) = decide (y ∈ L) :=
    fun y L => decide_eq_decide.2 (List.mem_map_of_injective φ.injective)
  have h3 : ([1, φ x, φ x ^ 2] : List (CV n)) = [1, x, x ^ 2].map φ := by simp
  have hp : ∀ y : CV n, powOneC (φ y) 3 = powOneC y 3 := fun y => by
    rw [← powOneC_eq', ← powOneC_eq', decide_eq_decide, ← map_pow]
    exact map_eq_one_iff φ φ.injective
  have he : ∀ a b : CV n, eq22C (φ a) (φ b) (φ b) (φ a) = eq22C a b b a := fun a b => by
    rw [eq22C_eq, eq22C_eq, ← map_mul, ← map_mul]
    exact decide_eq_decide.2 φ.injective.eq_iff
  have hl : ∀ y : CV n, pow3list (φ x) (φ y) = (pow3list x y).map φ := fun y =>
    (pow3list_map φ.toMonoidHom x y).symm
  simp only [List.all_map, Function.comp_def, hp, he, h3, hm, hl]

theorem kCent3Perm (x : CV n) {C C' : List (CV n)} (h : C.Perm C') :
    cent3atC x C = cent3atC x C' := by
  unfold cent3atC
  simp only [kAllPerm h]

theorem kCent3_cls (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (reps : List (CV n))
    (hcl : ((elemsC Q).filter fun x => powOneC x 3 && !decide (x = 1)).all
      (fun x => (elemsC Q).any fun g => reps.any fun r => eq22C g r x g) = true)
    (hr : reps.all (fun r => cent3atC r (centL (elemsC Q) r)) = true) :
    cent3C (elemsC Q) = true := by
  refine (kAll_filter (elemsC Q) (fun x => powOneC x 3 && !decide (x = 1))
    (fun x => cent3atC x (centL (elemsC Q) x))).trans ?_
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨g, hg, hgr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcl x hx)
  obtain ⟨r, hr', hgx⟩ := List.any_eq_true.1 hgr
  rw [eq22C_eq, decide_eq_true_iff] at hgx
  have hx' : x = g * r * g⁻¹ := eq_mul_inv_of_mul_eq hgx.symm
  rw [hx', kCent3Perm _ (kCentPerm Q hQ hg r)]
  exact (kCent3Map (MulAut.conj g) r _).trans (List.all_eq_true.1 hr r hr')

theorem kSolv_cls (QA QP : RawSchreierDatum n) (hP : ValidSchreier QP) (reps : List (CV n))
    (goods : List ℕ)
    (hcl : ((elemsC QA).filter fun τ => powOneC τ 2 && !decide (τ = 1)).all
      (fun τ => (elemsC QP).any fun g => reps.any fun r => eq22C g r τ g) = true)
    (hr : reps.all (fun r => decide ((centL (elemsC QP) r).length ∈ goods)) = true) :
    solvC (elemsC QA) (elemsC QP) goods = true := by
  refine (kAll_filter (elemsC QA) (fun τ => powOneC τ 2 && !decide (τ = 1))
    (fun τ => decide ((centL (elemsC QP) τ).length ∈ goods))).trans ?_
  rw [List.all_eq_true]
  intro τ hτ
  obtain ⟨g, hg, hgr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcl τ hτ)
  obtain ⟨r, hr', hgx⟩ := List.any_eq_true.1 hgr
  rw [eq22C_eq, decide_eq_true_iff] at hgx
  have hx' : τ = g * r * g⁻¹ := eq_mul_inv_of_mul_eq hgx.symm
  rw [hx', centL_conj QP hP hg r]
  exact List.all_eq_true.1 hr r hr'

end Conj

noncomputable def kReps3 : List (CV 26) :=
  [cOf PB, cOf (PB * PA * PB * PA * PB * PB * PA * PB * PA * PB)]

noncomputable def kReps2 : List (CV 26) := [cOf PA, cOf (sg0 ^ 3)]

noncomputable def kC3B (j : Nat) : Bool :=
  ((((elemsC QP).filter fun x => powOneC x 3 && !decide (x = 1)).drop (j * 104)).take 104).all
    fun x => (elemsC QP).any fun g => kReps3.any fun r => eq22C g r x g

#kc_each kC3B 0 7

theorem kC3R : kReps3.all (fun r => cent3atC r (centL (elemsC QP) r)) = true := by decide +kernel

theorem kCent3 (hQP : ValidSchreier QP) : cent3C (elemsC QP) = true := by
  have hb : ∀ j < 7, kC3B j = true := by
    intro j hj
    interval_cases j
    exacts [kC3B0, kC3B1, kC3B2, kC3B3, kC3B4, kC3B5, kC3B6]
  exact kCent3_cls QP hQP kReps3 (PkEnum.all_of_chunks _ _ 104 7 (by decide +kernel) hb) kC3R

noncomputable def kSolvB (j : Nat) : Bool :=
  ((((elemsC QA).filter fun τ => powOneC τ 2 && !decide (τ = 1)).drop (j * 117)).take 117).all
    fun τ => (elemsC QP).any fun g => kReps2.any fun r => eq22C g r τ g

#kc_each kSolvB 0 3

theorem kSolvR : kReps2.all (fun r => decide ((centL (elemsC QP) r).length ∈ [48, 24])) = true := by
  decide +kernel

theorem kSolv (hQP : ValidSchreier QP) : solvC (elemsC QA) (elemsC QP) [48, 24] = true := by
  have hb : ∀ j < 3, kSolvB j = true := by
    intro j hj
    interval_cases j
    exacts [kSolvB0, kSolvB1, kSolvB2]
  exact kSolv_cls QA QP hQP kReps2 [48, 24] (PkEnum.all_of_chunks _ _ 117 3 (by decide +kernel) hb)
    kSolvR

theorem kAll_false_of_block {α : Type*} (l : List α) (p : α → Bool) (k c : Nat)
    (h : ((l.drop k).take c).all p = false) : l.all p = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro hl
  apply h
  rw [List.all_eq_true] at hl ⊢
  intro x hx
  exact hl x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem kSolv_neg : solvC (elemsC QA) (elemsC QP) [48] = false :=
  (kAll_filter (elemsC QA) (fun τ => powOneC τ 2 && !decide (τ = 1))
    (fun τ => decide ((centL (elemsC QP) τ).length ∈ [48]))).trans
    (kAll_false_of_block _ _ 40 20 (by decide +kernel))

end CFSG.Certificates.Kernel.PkCV.KGrp.K5120
