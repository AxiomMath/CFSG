module

public import CFSG.GH74.KGroups.M11TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK

theorem qs_5126K : schP QS = true ∧ orderV QS = 16 := by
  constructor <;> decide +kernel

@[expose] def sqOnePk {n : Nat} (a : VP n) : Bool :=
  (List.range n).all fun i => fd (wd n) a.1.1 (fd (wd n) a.1.1 i) == i

@[expose] def isOnePk {n : Nat} (a : VP n) : Bool :=
  (List.range n).all fun i => fd (wd n) a.1.1 i == i

@[expose] def conjEqPk {n : Nat} (g t u : VP n) : Bool :=
  (List.range n).all fun i =>
    fd (wd n) g.1.1 (fd (wd n) t.1.1 (fd (wd n) g.1.2 i)) == fd (wd n) u.1.1 i

@[expose] def invConjPk {n : Nat} (L : List (VP n)) (t : VP n) : Bool :=
  L.all fun u => bif sqOnePk u && !isOnePk u then L.any fun g => conjEqPk g t u else true

theorem all_range_beq_iff {n : Nat} (f g : Nat → Nat) :
    ((List.range n).all fun i => f i == g i) = true ↔ ∀ i < n, f i = g i := by
  simp [List.all_eq_true]

theorem perm_eq_iff_val {n : Nat} (σ τ : Equiv.Perm (Fin n)) :
    σ = τ ↔ ∀ i < n, ∀ h : i < n, (σ ⟨i, h⟩ : Nat) = τ ⟨i, h⟩ := by
  constructor
  · rintro rfl i _ _
    rfl
  · intro h
    exact Equiv.ext fun i => Fin.ext (h i i.2 i.2)

theorem decide_eq_of_iff {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    decide p = b := by
  cases b <;> simp_all

theorem sqOnePk_eq {n : Nat} (a : VP n) : decide (pkp a ^ 2 = 1) = sqOnePk a := by
  refine decide_eq_of_iff ?_
  rw [sq, perm_eq_iff_val, sqOnePk, all_range_beq_iff]
  exact ⟨fun h i hi => h i hi hi, fun h i hi _ => h i hi⟩

theorem isOnePk_iff {n : Nat} (a : VP n) : isOnePk a = true ↔ pkp a = 1 := by
  rw [perm_eq_iff_val, isOnePk, all_range_beq_iff]
  exact ⟨fun h i hi _ => h i hi, fun h i hi => h i hi hi⟩

theorem isOnePk_eq {n : Nat} (a : VP n) : decide (pkp a ≠ 1) = !isOnePk a := by
  refine decide_eq_of_iff ?_
  simp only [ne_eq, ← isOnePk_iff]
  cases isOnePk a <;> simp

theorem conjEqPk_eq {n : Nat} (g t u : VP n) :
    decide (pkp g * pkp t * (pkp g)⁻¹ = pkp u) = conjEqPk g t u := by
  refine decide_eq_of_iff ?_
  rw [perm_eq_iff_val, conjEqPk, all_range_beq_iff]
  exact ⟨fun h i hi => h i hi hi, fun h i hi _ => h i hi⟩

theorem invConjCheck_map_pkp {n : Nat} (L : List (VP n)) (t : VP n) :
    invConjCheck (L.map pkp) (pkp t) = invConjPk L t := by
  unfold invConjCheck invConjPk
  simp only [List.all_map, List.any_map, Function.comp_def, sqOnePk_eq, isOnePk_eq, conjEqPk_eq]

theorem inv_5126K_pk : invConjPk (enumV (strongV Q) Q.base) (codeV t0) = true := by
  decide +kernel

theorem inv_5126K : invConjCheck (elemsV Q) t0 = true := by
  rw [elemsV, ← pkp_codeV t0, invConjCheck_map_pkp]
  exact inv_5126K_pk

theorem small_5126K : smallCheck (elemsV QS) s0 = true := by
  decide +kernel

theorem rel_5126K : sR ^ 8 = 1 ∧ sT ^ 2 = 1 ∧ sT * sR * sT⁻¹ = sR ^ 3 ∧
    (∀ i : Fin 8, ∀ e : Fin 2, sR ^ (i : ℕ) * sT ^ (e : ℕ) = 1 → i = 0 ∧ e = 0) := by
  decide +kernel

theorem le_5126K : (QS.original.toList.all fun g => siftP Q g 0) = true := by
  decide +kernel

theorem neg5126K : invConjCheck (elemsV Q) 1 = false := by
  decide +kernel

theorem neg5126K' : smallCheck (elemsV QS) 1 = false := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
