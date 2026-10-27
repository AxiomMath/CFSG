module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Fi24.Tables
import Certificates.Kernel.Fi24.Tables1
import Certificates.Kernel.Fi24.Tables2
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2
  TauCeti TauCeti.Sporadic

theorem card_le_step' {G : Type*} [Group G] {H K : Subgroup G} {N M : ℕ}
    (h : H.relIndex K ≠ 0 ∧ H.relIndex K ≤ N) (hH : Nat.card H ≠ 0 ∧ Nat.card H ≤ M) :
    Nat.card K ≠ 0 ∧ Nat.card K ≤ N * M := by
  have hf : Finite H := Nat.finite_of_card_ne_zero hH.1
  have hi : (H ⊓ K).relIndex K = H.relIndex K := Subgroup.inf_relIndex_right H K
  have hf' : Finite (H ⊓ K : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : H ⊓ K ≤ H))
  have hc : Nat.card (H ⊓ K : Subgroup G) ≠ 0 ∧ Nat.card (H ⊓ K : Subgroup G) ≤ M :=
    ⟨Nat.card_pos.ne', (Subgroup.card_le_of_le inf_le_left).trans hH.2⟩
  exact KB.card_le_step ⟨inf_le_right, hi ▸ h.1, hi ▸ h.2⟩ hc

theorem img_eq {G : Type*} (f : ℕ → G) (a b : ℕ) (h : ∀ x, x < a ↔ 2 * x < b) :
    f '' {j | j < a} = f '' {g | 2 * g < b} := by
  congr 1
  ext x
  exact h x

theorem fi24aut_card : Finite Fi24AutomorphismGroup ∧
    Nat.card Fi24AutomorphismGroup ≤ 2510411418381323442585600 := by
  have t1 := s1
  have t2 := s2
  have t3 := s3
  have t4 := s4
  have t5 := s5
  have t6 := s6
  have t7 := s7
  have t8 := s8
  have t9 := s9
  have t10 := s10
  have t11 := s11
  unfold Tab at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
  rw [img_eq cg2 (nat_lit 10) (nat_lit 20) (fun x => by change x < 10 ↔ 2 * x < 20; omega)] at t1
  rw [img_eq cg3 (nat_lit 9) (nat_lit 18) (fun x => by change x < 9 ↔ 2 * x < 18; omega)] at t2
  rw [img_eq cg4 (nat_lit 8) (nat_lit 16) (fun x => by change x < 8 ↔ 2 * x < 16; omega)] at t3
  rw [img_eq cg5 (nat_lit 7) (nat_lit 14) (fun x => by change x < 7 ↔ 2 * x < 14; omega)] at t4
  rw [img_eq cg6 (nat_lit 6) (nat_lit 12) (fun x => by change x < 6 ↔ 2 * x < 12; omega)] at t5
  rw [img_eq cg7 (nat_lit 5) (nat_lit 10) (fun x => by change x < 5 ↔ 2 * x < 10; omega)] at t6
  rw [img_eq cg8 (nat_lit 4) (nat_lit 8) (fun x => by change x < 4 ↔ 2 * x < 8; omega)] at t7
  rw [img_eq cg9 (nat_lit 3) (nat_lit 6) (fun x => by change x < 3 ↔ 2 * x < 6; omega)] at t8
  rw [img_eq cg10 (nat_lit 2) (nat_lit 4) (fun x => by change x < 2 ↔ 2 * x < 4; omega)] at t9
  rw [img_eq cg11 (nat_lit 1) (nat_lit 2) (fun x => by change x < 1 ↔ 2 * x < 2; omega)] at t10
  have e0 : (fun j => bval cg11 (wWord (CFSG.KD.F11.selST j)) (wLen (CFSG.KD.F11.selST j))) ''
      {j | j < nat_lit 0} = ∅ :=
    Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun j hj => Nat.not_lt_zero j hj)
  rw [e0, Subgroup.closure_empty, Subgroup.relIndex_bot_left] at t11
  have etop : Subgroup.closure (g0 '' {g | 2 * g < nat_lit 24}) = ⊤ := by
    have e : {g : ℕ | 2 * g < nat_lit 24} = {g | g < 12} := by
      ext g
      change 2 * g < 24 ↔ g < 12
      omega
    rw [e]
    exact closure_pgen _
  rw [etop] at t1
  have c := card_le_step' t1 <| card_le_step' t2 <| card_le_step' t3 <| card_le_step' t4 <|
    card_le_step' t5 <| card_le_step' t6 <| card_le_step' t7 <| card_le_step' t8 <|
    card_le_step' t9 <| card_le_step' t10 t11
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

theorem fi24ParityHom_surjective : Function.Surjective fi24ParityHom := by
  intro y
  obtain ⟨z, rfl⟩ : ∃ z : ZMod 2, Multiplicative.ofAdd z = y := ⟨y.toAdd, rfl⟩
  fin_cases z
  · exact ⟨1, map_one _⟩
  · exact ⟨PresentedGroup.of 0, fi24ParityHom_of 0⟩

theorem fi24Prime : Finite TauCeti.SporadicName.Fi24Prime.Group ∧
    Nat.card TauCeti.SporadicName.Fi24Prime.Group ≤ 1255205709190661721292800 := by
  obtain ⟨hf, hc⟩ := fi24aut_card
  have e : TauCeti.SporadicName.Fi24Prime.Group ≃* ↥(commutator Fi24AutomorphismGroup) :=
    fi24PrimeGroupMulEquivCommutator
  have hi : (fi24ParityHom.ker).index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr fi24ParityHom_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  have hm := Subgroup.card_mul_index fi24ParityHom.ker
  rw [hi] at hm
  rw [commutator_fi24AutomorphismGroup_eq_ker_fi24ParityHom] at e
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  omega

end CertificateChecks.KernelFi24

end
