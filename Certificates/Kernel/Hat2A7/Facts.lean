module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates.Kernel.Hat2A7

open CFSG.ClassicalInvolution.Hat2A7
open Equiv Equiv.Perm

@[expose] def tau1 : Perm (Fin 7) := swap 0 1

@[expose] def tau2 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def tau3 : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5

theorem cycleType_invol {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hs := sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hs
  rw [hn, ← hs]
  congr 1
  omega

theorem isConj_tau {σ : Perm (Fin 7)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    IsConj tau1 σ ∨ IsConj tau2 σ ∨ IsConj tau3 σ := by
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hle := sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  have e1 : tau1.cycleType = Multiset.replicate 1 2 := by
    rw [cycleType_invol (by decide +kernel) (by decide +kernel),
      (by decide +kernel : tau1.support.card = 2)]
  have e2 : tau2.cycleType = Multiset.replicate 2 2 := by
    rw [cycleType_invol (by decide +kernel) (by decide +kernel),
      (by decide +kernel : tau2.support.card = 4)]
  have e3 : tau3.cycleType = Multiset.replicate 3 2 := by
    rw [cycleType_invol (by decide +kernel) (by decide +kernel),
      (by decide +kernel : tau3.support.card = 6)]
  have hn2 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn2 with rfl | rfl | rfl
  · exact Or.inl (isConj_iff_cycleType_eq.2 (by rw [hn, e1]))
  · exact Or.inr (Or.inl (isConj_iff_cycleType_eq.2 (by rw [hn, e2])))
  · exact Or.inr (Or.inr (isConj_iff_cycleType_eq.2 (by rw [hn, e3])))

theorem a7_involution_conj :
    ∀ y : A7, y ≠ 1 → y * y = 1 → ∃ g : A7, g * tD * g⁻¹ = y := by
  intro y hy1 hy2
  have h2 : (y : Perm (Fin 7)) * y = 1 := congrArg Subtype.val hy2
  have h1 : (y : Perm (Fin 7)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hs : sign (y : Perm (Fin 7)) = 1 := y.2
  have hc : IsConj ((tD : A7) : Perm (Fin 7)) (y : Perm (Fin 7)) := by
    have hsc : ∀ τ : Perm (Fin 7), IsConj τ (y : Perm (Fin 7)) → sign τ = 1 := fun τ h => by
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      rwa [← hc, map_mul, map_mul, sign_inv, mul_comm, ← mul_assoc, Int.units_mul_self,
        one_mul] at hs
    rcases isConj_tau h2 h1 with h | h | h
    · exact absurd (hsc _ h) (by decide +kernel)
    · exact h
    · exact absurd (hsc _ h) (by decide +kernel)
  exact isConj_iff.1 (alternatingGroup.isConj_of hc (by decide +kernel))

@[expose] def commTable (a b : Fin 7) : Fin 7 → Fin 7 :=
  let t : Perm (Fin 7) := tD
  let s : Perm (Fin 7) := sD
  ![a, t a, t (s (t a)), s (t a), b, s b, 6]

theorem commTable_invol : ∀ a b : Fin 7,
    (∀ x, commTable a b ((tD : Perm (Fin 7)) x) = (tD : Perm (Fin 7)) (commTable a b x)) →
    (∀ x, commTable a b ((sD : Perm (Fin 7)) x) = (sD : Perm (Fin 7)) (commTable a b x)) →
    (∀ x y, commTable a b x = commTable a b y → x = y) →
    ∀ x, commTable a b (commTable a b x) = x := by
  decide +kernel

theorem common_fixed : ∀ c : Fin 7,
    (tD : Perm (Fin 7)) c = c → (sD : Perm (Fin 7)) c = c → c = 6 := by
  decide +kernel

theorem sq_eq_one_of_commute_gens :
    ∀ σ : Perm (Fin 7), σ * (sD : Perm (Fin 7)) = (sD : Perm (Fin 7)) * σ →
      σ * (tD : Perm (Fin 7)) = (tD : Perm (Fin 7)) * σ → σ * σ = 1 := by
  intro σ hs ht
  have hs' : ∀ x, σ ((sD : Perm (Fin 7)) x) = (sD : Perm (Fin 7)) (σ x) := fun x => by
    simpa only [Perm.mul_apply] using congrArg (fun p : Perm (Fin 7) => p x) hs
  have ht' : ∀ x, σ ((tD : Perm (Fin 7)) x) = (tD : Perm (Fin 7)) (σ x) := fun x => by
    simpa only [Perm.mul_apply] using congrArg (fun p : Perm (Fin 7) => p x) ht
  have h6 : σ 6 = 6 := common_fixed _ (by rw [← ht']; rfl) (by rw [← hs']; rfl)
  have h1 : σ 1 = (tD : Perm (Fin 7)) (σ 0) := ht' 0
  have h3 : σ 3 = (sD : Perm (Fin 7)) (σ 1) := hs' 1
  have h2 : σ 2 = (tD : Perm (Fin 7)) (σ 3) := ht' 3
  have h5 : σ 5 = (sD : Perm (Fin 7)) (σ 4) := hs' 4
  have hf : ∀ x, σ x = commTable (σ 0) (σ 4) x := by
    intro x
    fin_cases x
    · rfl
    · exact h1
    · change σ 2 = commTable (σ 0) (σ 4) 2
      rw [h2, h3, h1]
      rfl
    · change σ 3 = commTable (σ 0) (σ 4) 3
      rw [h3, h1]
      rfl
    · rfl
    · exact h5
    · exact h6
  have key := commTable_invol (σ 0) (σ 4)
    (fun x => (hf _).symm.trans ((ht' x).trans (congrArg _ (hf x))))
    (fun x => (hf _).symm.trans ((hs' x).trans (congrArg _ (hf x))))
    (fun x y h => σ.injective ((hf x).trans (h.trans (hf y).symm)))
  refine Equiv.Perm.ext fun x => ?_
  rw [Perm.mul_apply, Perm.one_apply, hf (σ x), hf x]
  exact key x

theorem conj_witness (g τ w : Perm (Fin 7)) (h1 : w⁻¹ * τ * w ≠ τ)
    (h2 : (w⁻¹ * τ * w) * τ = τ * (w⁻¹ * τ * w)) :
    (g * w * g⁻¹)⁻¹ * (g * τ * g⁻¹) * (g * w * g⁻¹) ≠ g * τ * g⁻¹ ∧
      ((g * w * g⁻¹)⁻¹ * (g * τ * g⁻¹) * (g * w * g⁻¹)) * (g * τ * g⁻¹) =
        (g * τ * g⁻¹) * ((g * w * g⁻¹)⁻¹ * (g * τ * g⁻¹) * (g * w * g⁻¹)) := by
  have e : (g * w * g⁻¹)⁻¹ * (g * τ * g⁻¹) * (g * w * g⁻¹) = g * (w⁻¹ * τ * w) * g⁻¹ := by
    group
  rw [e]
  refine ⟨fun h => h1 ?_, ?_⟩
  · have := congrArg (fun p => g⁻¹ * p * g) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
  · calc g * (w⁻¹ * τ * w) * g⁻¹ * (g * τ * g⁻¹) = g * ((w⁻¹ * τ * w) * τ) * g⁻¹ := by group
      _ = g * (τ * (w⁻¹ * τ * w)) * g⁻¹ := by rw [h2]
      _ = g * τ * g⁻¹ * (g * (w⁻¹ * τ * w) * g⁻¹) := by group

theorem exists_commuting_conj :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → σ ≠ 1 →
      ∃ a : A7, (a : Perm (Fin 7))⁻¹ * σ * a ≠ σ ∧
        ((a : Perm (Fin 7))⁻¹ * σ * a) * σ = σ * ((a : Perm (Fin 7))⁻¹ * σ * a) := by
  intro σ h2 h1
  have key : ∀ τ w : Perm (Fin 7), IsConj τ σ → w ∈ alternatingGroup (Fin 7) →
      w⁻¹ * τ * w ≠ τ → (w⁻¹ * τ * w) * τ = τ * (w⁻¹ * τ * w) →
      ∃ a : A7, (a : Perm (Fin 7))⁻¹ * σ * a ≠ σ ∧
        ((a : Perm (Fin 7))⁻¹ * σ * a) * σ = σ * ((a : Perm (Fin 7))⁻¹ * σ * a) := by
    intro τ w hc hw hne hcomm
    obtain ⟨g, rfl⟩ := isConj_iff.1 hc
    exact ⟨⟨g * w * g⁻¹, (alternatingGroup.normal (α := Fin 7)).conj_mem w hw g⟩,
      conj_witness g τ w hne hcomm⟩
  rcases isConj_tau h2 h1 with h | h | h
  · exact key tau1 (swap 0 2 * swap 1 3) h (mem_alternatingGroup.2 (by decide +kernel))
      (by decide +kernel) (by decide +kernel)
  · exact key tau2 (swap 0 4 * swap 1 5) h (mem_alternatingGroup.2 (by decide +kernel))
      (by decide +kernel) (by decide +kernel)
  · exact key tau3 (swap 1 2 * swap 4 5) h (mem_alternatingGroup.2 (by decide +kernel))
      (by decide +kernel) (by decide +kernel)

theorem card_even_comm_conj (g τ : Perm (Fin 7)) :
    Fintype.card {p : Perm (Fin 7) // p * (g * τ * g⁻¹) = (g * τ * g⁻¹) * p ∧ sign p = 1} =
      Fintype.card {p : Perm (Fin 7) // p * τ = τ * p ∧ sign p = 1} := by
  refine (Fintype.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun p => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, map_mul,
    sign_inv]
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨?_, by rw [mul_right_comm, Int.units_mul_self, one_mul]; exact hs⟩
    calc g * p * g⁻¹ * (g * τ * g⁻¹) = g * (p * τ) * g⁻¹ := by group
      _ = g * (τ * p) * g⁻¹ := by rw [hc]
      _ = g * τ * g⁻¹ * (g * p * g⁻¹) := by group
  · rintro ⟨hc, hs⟩
    refine ⟨?_, by rwa [mul_right_comm, Int.units_mul_self, one_mul] at hs⟩
    calc p * τ = g⁻¹ * (g * p * g⁻¹ * (g * τ * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * τ * g⁻¹ * (g * p * g⁻¹)) * g := by rw [hc]
      _ = τ * p := by group

theorem card_centralizer_eq_two_mul (τ u : Perm (Fin 7)) (hu : u * τ = τ * u)
    (hus : sign u = -1) :
    Nat.card (Subgroup.centralizer {τ}) =
      2 * Fintype.card {p : Perm (Fin 7) // p * τ = τ * p ∧ sign p = 1} := by
  classical
  have hC : Nat.card (Subgroup.centralizer {τ}) =
      (Finset.univ.filter fun p : Perm (Fin 7) => p * τ = τ * p).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun p => by
      rw [Subgroup.mem_centralizer_singleton_iff, eq_comm])
  have hE : Fintype.card {p : Perm (Fin 7) // p * τ = τ * p ∧ sign p = 1} =
      ((Finset.univ.filter fun p : Perm (Fin 7) => p * τ = τ * p).filter
        fun p => sign p = 1).card := by
    rw [Finset.filter_filter, Fintype.card_subtype]
  have hO : ((Finset.univ.filter fun p : Perm (Fin 7) => p * τ = τ * p).filter
        fun p => ¬ sign p = 1).card =
      ((Finset.univ.filter fun p : Perm (Fin 7) => p * τ = τ * p).filter
        fun p => sign p = 1).card := by
    refine Finset.card_bij' (fun p _ => u * p) (fun p _ => u⁻¹ * p) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨?_, ?_⟩
      · rw [mul_assoc, hp.1, ← mul_assoc, hu, mul_assoc]
      · rw [map_mul, hus, (Int.units_eq_one_or (sign p)).resolve_left hp.2]; rfl
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hu' : u⁻¹ * τ = τ * u⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hu, mul_inv_cancel_right]
      refine ⟨?_, ?_⟩
      · rw [mul_assoc, hp.1, ← mul_assoc, hu', mul_assoc]
      · rw [map_mul, sign_inv, hus, hp.2]; decide
    · intro p _; simp
    · intro p _; simp
  rw [hC, hE, ← Finset.card_filter_add_card_filter_not (p := fun p => sign p = 1), hO,
    two_mul]

theorem card_even_comm_tau {τ : Perm (Fin 7)} {k : ℕ} (h2 : τ * τ = 1) (h1 : τ ≠ 1)
    (hsupp : τ.support.card = k * 2) (hk1 : k ≠ 0) (hu : swap 0 1 * τ = τ * swap 0 1)
    (hc : ((7 - k * 2).factorial * 2 ^ k * k.factorial) % 32 = 16) :
    Fintype.card {p : Perm (Fin 7) // p * τ = τ * p ∧ sign p = 1} % 16 = 8 := by
  have hk : τ.cycleType = Multiset.replicate k 2 := by
    rw [cycleType_invol h2 h1, hsupp, Nat.mul_div_cancel _ two_pos]
  have h := card_centralizer_eq_two_mul τ (swap 0 1) hu (sign_swap (by decide))
  rw [nat_card_centralizer, hk, Multiset.sum_replicate, Multiset.prod_replicate,
    Multiset.toFinset_replicate, ite_eq_right hk1, Finset.prod_singleton,
    Multiset.count_replicate_self, Fintype.card_fin, smul_eq_mul] at h
  omega

theorem card_evenCentralizer_mod :
    ∀ σ : Perm (Fin 7), σ * σ = 1 →
      Fintype.card {a : A7 // (a : Perm (Fin 7)) * σ = σ * a} % 16 = 8 := by
  intro σ h2
  have e : Fintype.card {a : A7 // (a : Perm (Fin 7)) * σ = σ * a} =
      Fintype.card {p : Perm (Fin 7) // p * σ = σ * p ∧ sign p = 1} :=
    Fintype.card_congr
      { toFun := fun a => ⟨a.1.1, a.2, mem_alternatingGroup.1 a.1.2⟩
        invFun := fun p => ⟨⟨p.1, mem_alternatingGroup.2 p.2.2⟩, p.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e]
  by_cases h1 : σ = 1
  · subst h1
    have h := Fintype.card_congr (Equiv.subtypeEquivRight
      (p := fun p : Perm (Fin 7) => p * 1 = 1 * p ∧ sign p = 1)
      (q := fun p : Perm (Fin 7) => p ∈ alternatingGroup (Fin 7)) fun p => by
        simp [mem_alternatingGroup])
    have hA := two_mul_card_alternatingGroup (α := Fin 7)
    rw [Fintype.card_perm, Fintype.card_fin] at hA
    have hA' : Fintype.card (alternatingGroup (Fin 7)) = 2520 := by
      have : Nat.factorial 7 = 5040 := by decide
      omega
    have h3 : Fintype.card {p : Perm (Fin 7) // p ∈ alternatingGroup (Fin 7)} = 2520 := by
      rw [← hA']
    rw [h, h3]
  · rcases isConj_tau h2 h1 with h | h | h <;> obtain ⟨g, rfl⟩ := isConj_iff.1 h <;>
      rw [card_even_comm_conj]
    · exact card_even_comm_tau (k := 1) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    · exact card_even_comm_tau (k := 2) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    · exact card_even_comm_tau (k := 3) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)

end Certificates.Kernel.Hat2A7
