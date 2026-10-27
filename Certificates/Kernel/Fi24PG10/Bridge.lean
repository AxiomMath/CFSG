module

public import Certificates.Kernel.Fi24PG10.Rels
import Certificates.Kernel.Fi24PG10.Tables1

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

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

theorem pg10_card : Finite G10 ∧ Nat.card G10 ≤ 4089470473293004800 := by
  have u1 := t1
  have u2 := t2
  have u3 := t3
  have u4 := t4
  have u5 := t5
  have u6 := t6
  unfold Tab at u1 u2 u3 u4 u5 u6
  rw [sub_img sub1 (L := nat_lit 18) rfl] at u1
  rw [sub_img sub2 (L := nat_lit 16) rfl] at u2
  rw [sub_img sub3 (L := nat_lit 14) rfl] at u3
  rw [sub_img sub4 (L := nat_lit 12) rfl] at u4
  rw [sub_img sub5 (L := nat_lit 10) rfl] at u5
  have e0 : (fun j => bval (gen A6) (wWord (CFSG.KD.PG10P6.selST j)) (wLen (CFSG.KD.PG10P6.selST j))) ''
      {j | j < nat_lit 0} = ∅ :=
    Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun j hj => Nat.not_lt_zero j hj)
  rw [e0, Subgroup.closure_empty, Subgroup.relIndex_bot_left] at u6
  rw [closure_gen1] at u1
  have c := card_le_step' u1 <| card_le_step' u2 <| card_le_step' u3 <| card_le_step' u4 <|
    card_le_step' u5 u6
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

end CertificateChecks.KernelPG10

end
