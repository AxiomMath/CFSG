module

public import Certificates.Kernel.U62K.Lift
public import Certificates.Kernel.U62K.Group

public section

namespace CertificateChecks.U62Assemble

open Subgroup CFSG.EvenSporadicStandard.Induction.Fi CertificateChecks.U62Lift
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi23 (J lvl slvl sylG)


@[expose] noncomputable def T' : Subgroup CFSG.Sporadic.Fi23.J := slvl 0 ⊓ stabAt 31671 14566

theorem slvl_zero_eq :
    slvl 0 = Subgroup.closure {g | ∃ l < 42, CFSG.Perm.pairG sylG l = g} := by
  change CFSG.Perm.lettersGroup _ _ = _
  unfold CFSG.Perm.lettersGroup
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, CFSG.Perm.mem_levelLetters_zero, CFSG.Sporadic.Fi23.LS_size]
  rfl

theorem orbit_T (hL : ∀ l < 42, InTwo 31671 14566 18249 (CFSG.Perm.pairG sylG l)) :
    ∀ x ∈ slvl 0, InTwo 31671 14566 18249 x := by
  rw [slvl_zero_eq]
  exact orbit_two (by norm_num) fun _ ⟨l, hl, e⟩ => e ▸ hL l hl

theorem fix_T (hL : ∀ l < 42, idx 31671 (CFSG.Perm.pairG sylG l) 2776 = 2776) :
    ∀ x ∈ slvl 0, idx 31671 x 2776 = 2776 := by
  rw [slvl_zero_eq]
  exact fix_closure fun _ ⟨l, hl, e⟩ => e ▸ hL l hl

theorem card_T'
    (hL : ∀ l < 42, InTwo 31671 14566 18249 (CFSG.Perm.pairG sylG l))
    {t : CFSG.Sporadic.Fi23.J} (htT : t ∈ slvl 0) (ht : idx 31671 t 14566 = 18249) :
    Nat.card T' = 131072 := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  have h := card_stab_two (slvl 0) (by norm_num) (orbit_T hL) htT ht
  rw [CFSG.Sporadic.Fi23.card_slvl_zero] at h
  change Nat.card ↥(slvl 0 ⊓ stabAt 31671 14566) = 131072
  omega

theorem conj_le (hp : ∀ l < 42, idx 31671 (CFSG.Perm.pairG sylG l) 2776 = 2776) {g : CFSG.Sporadic.Fi23.J}
    (hg0 : idx 31671 g 0 = 2776) (hg1 : idx 31671 g 1 = 14566) :
    ∀ x ∈ T', g⁻¹ * x * g ∈ lvl 2 := by
  rintro x ⟨hx, hxq⟩
  have hxq' : idx 31671 x 14566 = 14566 := hxq
  have hxp := fix_T hp x hx
  rw [lvl_two_iff]
  simp only [idx_mul]
  rw [hg0, hg1, hxp, hxq']
  constructor
  · conv_lhs => rw [← hg0]
    exact idx_inv_idx g 0
  · conv_lhs => rw [← hg1]
    exact idx_inv_idx g 1

theorem facts_of
    (hL : ∀ l < 42, InTwo 31671 14566 18249 (CFSG.Perm.pairG sylG l))
    (hp : ∀ l < 42, idx 31671 (CFSG.Perm.pairG sylG l) 2776 = 2776)
    {t : CFSG.Sporadic.Fi23.J} (htT : t ∈ slvl 0) (ht : idx 31671 t 14566 = 18249)
    {g : CFSG.Sporadic.Fi23.J} (hg0 : idx 31671 g 0 = 2776) (hg1 : idx 31671 g 1 = 14566)
    (E : Subgroup ↥T') (X : Set ↥T')
    (hEl : ∀ x, IsLargeInvAt 14 x → x ∈ E)
    (hEc : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u) (hEsq : ∀ u ∈ E, u * u = 1)
    (hXl : ∀ x ∈ X, IsLargeInvAt 14 x) (hXc : Nat.card (centralizer X) ≤ Nat.card E)
    (hE : 2 ^ 11 ≤ Nat.card E)
    {x y : CFSG.Sporadic.Fi23.J} (hx : idx 31671 x 0 = 0 ∧ idx 31671 x 1 = 1)
    (hy : idx 31671 y 0 = 0 ∧ idx 31671 y 1 = 1)
    (hxy : x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d) :
    CFSG.EvenSporadicStandard.Solomon78.InvolutionFixesElem ↥(lvl 2) 64 ∧
      ∃ x y : CFSG.Sporadic.Fi23.J, x ∈ lvl 2 ∧ y ∈ lvl 2 ∧ x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  have hlc := CertificateChecks.U62Group.largeCentralizer_eq 14 E X hEl hEc hXl hXc
  refine ⟨involutionFixesElem_of_conj T' (card_T' hL htT ht) g (conj_le hp hg0 hg1) ?_ ?_ ?_,
    comm_of hx hy hxy⟩
  · rw [hlc]; exact hEsq
  · rw [hlc]; exact hEc
  · rw [hlc]; exact hE

end CertificateChecks.U62Assemble
