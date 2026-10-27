module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversLarge
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi23T2Tab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CertificateChecks.U62Lift

open Subgroup CFSG.EvenSporadicStandard.Induction.Fi
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.EvenSporadicStandard.Solomon78 (InvolutionFixesElem)

section Idx

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] def InTwo (n q q' : ℕ) [MulAction G (Fin n)] (x : G) : Prop :=
  (idx n x q = q ∨ idx n x q = q') ∧ (idx n x q' = q ∨ idx n x q' = q')

theorem inTwo_mul {q q' : ℕ} {a b : G} (ha : InTwo n q q' a) (hb : InTwo n q q' b) :
    InTwo n q q' (a * b) := by
  unfold InTwo at *
  rw [idx_mul, idx_mul]
  rcases hb with ⟨h1 | h1, h2 | h2⟩ <;> rw [h1, h2] <;>
    exact ⟨by first | exact ha.1 | exact ha.2, by first | exact ha.1 | exact ha.2⟩

theorem inTwo_inv {q q' : ℕ} (hne : q ≠ q') {a : G} (ha : InTwo n q q' a) :
    InTwo n q q' a⁻¹ := by
  unfold InTwo at *
  have i1 := idx_inv_idx (n := n) a q
  have i2 := idx_inv_idx (n := n) a q'
  rcases ha with ⟨h1 | h1, h2 | h2⟩ <;> rw [h1] at i1 <;> rw [h2] at i2
  · exact absurd (i1.symm.trans i2) hne
  · exact ⟨Or.inl i1, Or.inr i2⟩
  · exact ⟨Or.inr i2, Or.inl i1⟩
  · exact absurd (i1.symm.trans i2) hne

theorem orbit_two {L : Set G} {q q' : ℕ} (hne : q ≠ q') (hL : ∀ l ∈ L, InTwo n q q' l) :
    ∀ x ∈ closure L, InTwo n q q' x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem l hl => exact hL l hl
  | one => exact ⟨Or.inl (idx_one q), Or.inr (idx_one q')⟩
  | mul a b _ _ ha hb => exact inTwo_mul ha hb
  | inv a _ ha => exact inTwo_inv hne ha

theorem fix_closure {L : Set G} {p : ℕ} (hL : ∀ l ∈ L, idx n l p = p) :
    ∀ x ∈ closure L, idx n x p = p := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem l hl => exact hL l hl
  | one => exact idx_one p
  | mul a b _ _ ha hb => rw [idx_mul, hb, ha]
  | inv a _ ha => rw [← ha, idx_inv_idx, ha]

@[expose] def stabAt (n q : ℕ) [MulAction G (Fin n)] : Subgroup G where
  carrier := {x | idx n x q = q}
  one_mem' := idx_one q
  mul_mem' {a b} ha hb := by
    have ha' : idx n a q = q := ha
    have hb' : idx n b q = q := hb
    change idx n (a * b) q = q
    rw [idx_mul, hb', ha']
  inv_mem' {a} ha := by
    have ha' : idx n a q = q := ha
    change idx n a⁻¹ q = q
    conv_lhs => rw [← ha']
    exact idx_inv_idx a q

theorem mem_stabAt {q : ℕ} {x : G} : x ∈ stabAt n q ↔ idx n x q = q := Iff.rfl

theorem card_stab_two [Finite G] (H : Subgroup G) {q q' : ℕ} (hne : q ≠ q')
    (horb : ∀ x ∈ H, InTwo n q q' x) {t : G} (htH : t ∈ H) (ht : idx n t q = q') :
    2 * Nat.card ↥(H ⊓ stabAt n q) = Nat.card H := by
  set K := (H ⊓ stabAt n q).subgroupOf H
  have hK : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htH⟩, fun b => ?_⟩
    simp only [K, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.mem_inf,
      mem_stabAt, b.2, H.mul_mem b.2 htH, true_and]
    obtain ⟨h1, h2⟩ := horb b b.2
    have i1 := idx_inv_idx (n := n) (b : G) q
    have i2 := idx_inv_idx (n := n) (b : G) q'
    rw [idx_mul, ht]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1] at i1
      rw [h2] at i2
      exact absurd (i1.symm.trans i2) hne
    · rw [h2, h1]
      simp [Xor', hne.symm]
    · rw [h2, h1]
      simp [Xor', hne.symm]
    · rw [h1] at i1
      rw [h2] at i2
      exact absurd (i1.symm.trans i2) hne
  have hc : Nat.card K = Nat.card ↥(H ⊓ stabAt n q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hc, ← hK, mul_comm]
  exact K.card_mul_index

end Idx

section J


open CFSG.Sporadic.Fi23 (J lvl)

theorem lvl_two_iff {x : CFSG.Sporadic.Fi23.J} : x ∈ lvl 2 ↔ idx 31671 x 0 = 0 ∧ idx 31671 x 1 = 1 := by
  constructor
  · intro hx
    have hx1 : x ∈ lvl 1 := CFSG.Perm.levelGroup_anti _ (by norm_num : 1 ≤ 2) hx
    refine ⟨(CFSG.Sporadic.Fi23.lvl_one_iff x).2 hx1, ?_⟩
    have h := (CFSG.Sporadic.Fi23.chain_facts'.2.1 1
      (by rw [CFSG.Sporadic.Fi23.chainBase_size]; norm_num) x hx1).2 hx
    rwa [CFSG.Sporadic.Fi23.chainBase_one] at h
  · rintro ⟨h0, h1⟩
    have hx1 : x ∈ lvl 1 := (CFSG.Sporadic.Fi23.lvl_one_iff x).1 h0
    refine (CFSG.Sporadic.Fi23.chain_facts'.2.1 1
      (by rw [CFSG.Sporadic.Fi23.chainBase_size]; norm_num) x hx1).1 ?_
    rw [CFSG.Sporadic.Fi23.chainBase_one]
    exact h1

theorem u_sylow_iso' {Tsub : Subgroup CFSG.Sporadic.Fi23.J} (hle : Tsub ≤ lvl 2) (hcard : Nat.card ↥Tsub = 131072) :
    ∀ S : Sylow 2 ↥(lvl 2), Nonempty (↥(S : Subgroup ↥(lvl 2)) ≃* ↥Tsub) := by
  intro S
  have hcardT : Nat.card ↥(Tsub.subgroupOf (lvl 2)) =
      2 ^ (Nat.card ↥(lvl 2)).factorization 2 := by
    rw [card_lvl_two, show (36787322880 : ℕ) = 2 ^ 17 * 280665 by norm_num,
      CFSG.EvenSporadicStandard.YS14.factorization_two_pow_mul 17 280665 (by norm_num),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
    norm_num
  let T₀ : Sylow 2 ↥(lvl 2) := Sylow.ofCard (Tsub.subgroupOf (lvl 2)) hcardT
  exact ⟨(Sylow.equiv S T₀).trans ((MulEquiv.subgroupCongr (Sylow.coe_ofCard _ _)).trans
    (Subgroup.subgroupOfEquivOfLe hle))⟩

theorem involutionFixesElem_of_conj (T : Subgroup CFSG.Sporadic.Fi23.J) (hT : Nat.card T = 131072) (g : CFSG.Sporadic.Fi23.J)
    (hg : ∀ x ∈ T, g⁻¹ * x * g ∈ lvl 2)
    (hsq : ∀ u ∈ largeCentralizer 14 ↥T, u * u = 1)
    (hcomm : ∀ u ∈ largeCentralizer 14 ↥T, ∀ v ∈ largeCentralizer 14 ↥T, u * v = v * u)
    (hcard : 2 ^ 11 ≤ Nat.card ↥(largeCentralizer 14 ↥T)) :
    InvolutionFixesElem ↥(lvl 2) 64 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  let f : J →* J := (MulAut.conj g⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective
  set Tsub := T.map f
  have hle : Tsub ≤ lvl 2 := by
    rintro _ ⟨x, hx, rfl⟩
    have e : f x = g⁻¹ * x * g := by
      simp [f, MulAut.conj_apply]
    rw [e]
    exact hg x hx
  have hcs : Nat.card Tsub = 131072 := by
    rw [← hT]
    exact (Nat.card_congr (T.equivMapOfInjective f hf).toEquiv).symm
  have hiso : ∀ S : Sylow 2 ↥(lvl 2), Nonempty (↥(S : Subgroup ↥(lvl 2)) ≃* ↥T) := fun S =>
    ⟨(Classical.choice (u_sylow_iso' hle hcs S)).trans (T.equivMapOfInjective f hf).symm⟩
  have h := @involutionFixesElem_of_sylow_largeCentralizer ↥(lvl 2) inferInstance inferInstance
    ↥T (Subgroup.toGroup _) 14 hiso hsq hcomm 11 6 hcard (by norm_num)
  rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h
  exact h

theorem comm_of {x y : CFSG.Sporadic.Fi23.J} (hx : idx 31671 x 0 = 0 ∧ idx 31671 x 1 = 1)
    (hy : idx 31671 y 0 = 0 ∧ idx 31671 y 1 = 1) (hxy : x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d) :
    ∃ x y : CFSG.Sporadic.Fi23.J, x ∈ lvl 2 ∧ y ∈ lvl 2 ∧ x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d :=
  ⟨x, y, lvl_two_iff.2 hx, lvl_two_iff.2 hy, hxy⟩

end J

end CertificateChecks.U62Lift
