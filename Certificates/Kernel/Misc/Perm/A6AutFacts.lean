module

public import Certificates.Kernel.Misc.Perm.A6Aut
public import CFSG.CGT.Foote82.T66.BASThreeA6Defs
public import CFSG.Certificates.Kernel.Misc.PermA6AutSound
public import CFSG.Certificates.Kernel.Misc.PermGH23Clos
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.LocalQTPermSound
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelMisc.A6Aut

open Equiv CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CFSG.KC.Misc.A6Aut
  CFSG.OddStandard.SmallF3.HarrisU33.Outside

@[expose] def fin6 : Fin 6 ≃ {i : Fin 8 // (i : ℕ) < 6} where
  toFun i := ⟨Fin.castLE (by norm_num) i, i.isLt⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def emb : alternatingGroup (Fin 6) →* Perm (Fin 8) :=
  (Perm.extendDomainHom fin6).comp (alternatingGroup (Fin 6)).subtype

@[expose] def enc6 (g : alternatingGroup (Fin 6)) : ℕ := gh23Code (emb g)

theorem enc6_enc : ClosEnc enc6 mul8 one8 where
  enc_one := by rw [enc6, map_one]; exact gh23_enc.enc_one
  enc_mul a b := by rw [enc6, map_mul]; exact gh23_enc.enc_mul _ _
  inj := gh23_enc.inj.comp ((Perm.extendDomainHom_injective fin6).comp Subtype.val_injective)

@[expose] def a6x : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    decide⟩

@[expose] def a6y : alternatingGroup (Fin 6) :=
  ⟨swap 0 4 * swap 0 2 * swap 0 1 * swap 3 5, by
    rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    decide⟩

theorem enc6_x : xC = enc6 a6x := by decide +kernel

theorem enc6_y : yC = enc6 a6y := by decide +kernel

theorem x_sq : a6x * a6x = 1 := by decide +kernel

theorem y_four : a6y * a6y * (a6y * a6y) = 1 := by decide +kernel

theorem xy_five : a6x * a6y * (a6x * a6y * (a6x * a6y * (a6x * a6y * (a6x * a6y)))) = 1 := by
  decide +kernel

theorem xyy_five :
    a6x * (a6y * a6y) * (a6x * (a6y * a6y) * (a6x * (a6y * a6y) *
      (a6x * (a6y * a6y) * (a6x * (a6y * a6y))))) = 1 := by
  decide +kernel

theorem tree_ok : ∀ k < 360, treeAt mul8 one8 genC 2 E P k = true := fun k hk =>
  (allR_iff 0 360 _).1 (TK.all 0 (by norm_num)) k (Nat.zero_le _) (by omega)

theorem sort_ok : ∀ i < 360, sortAt 360 E S i = true := fun k hk =>
  (allR_iff 0 360 _).1 (SK.all 0 (by norm_num)) k (Nat.zero_le _) (by omega)

theorem closed_ok : ∀ k < 360, closedAt mul8 genC 2 360 E C k = true := fun k hk =>
  (allR_iff 0 360 _).1 (CK.all 0 (by norm_num)) k (Nat.zero_le _) (by omega)

theorem rec2_ok : ∀ k < 360, rec2At E L2 R2 46 k = true := fun k hk =>
  (allR_iff 0 360 _).1 (P.andB_iff.1 (RK.all 0 (by norm_num))).1 k (Nat.zero_le _) (by omega)

theorem rec4_ok : ∀ k < 360, rec4At E L4 R4 136 k = true := fun k hk =>
  (allR_iff 0 360 _).1 (P.andB_iff.1 (RK.all 0 (by norm_num))).2 k (Nat.zero_le _) (by omega)

theorem involAutA6Cases_kernel : CFSG.CGT.Foote82.InvolAutA6Cases := by
  intro θ hθ hne
  have hG : ∀ j < [a6x, a6y].length, genC j = enc6 ([a6x, a6y].getD j 1) := by
    intro j hj
    have hj2 : j < 2 := hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact enc6_x
    · exact enc6_y
  obtain ⟨hall, -, hcl⟩ := clos_card_proved enc6_enc [a6x, a6y] hG (by norm_num : 0 < 360)
    tree_ok sort_ok
  obtain ⟨hcard, hmem⟩ := hcl closed_ok
  have htop : Subgroup.closure {g | g ∈ [a6x, a6y]} = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hfind : ∀ g, ∃ k < 360, enc6 g = E k := fun g =>
    hmem g (by rw [htop]; exact Subgroup.mem_top g)
  have hex : ∀ k < 360, ∃ g, enc6 g = E k := fun k hk => (hall k hk).imp fun _ h => h.2
  have hne' : ¬(θ.toMonoidHom a6x = a6x ∧ θ.toMonoidHom a6y = a6y) := by
    rintro ⟨hx, hy⟩
    obtain ⟨g, hg⟩ := hne
    apply hg
    have hS : Set.EqOn θ.toMonoidHom (MonoidHom.id _) {g | g ∈ [a6x, a6y]} := by
      intro z hz
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    exact MonoidHom.eqOn_closure hS (by rw [htop]; exact Subgroup.mem_top g)
  obtain ⟨iu, hiu, heu⟩ := hfind (θ a6x)
  obtain ⟨iv, hiv, hev⟩ := hfind (θ a6y)
  have h2 := rec2_ok iu hiu
  have h4 := rec4_ok iv hiv
  simp only [rec2At, rec4At, P.impB_iff, P.letB_eq, P.andB_iff, P.blt_iff, P.beq_iff] at h2 h4
  have hx2 := congrArg θ x_sq
  have hy4 := congrArg θ y_four
  simp only [map_mul, map_one] at hx2 hy4
  obtain ⟨hr, hL2⟩ := h2 (by rw [← heu, ← enc6_enc.enc_mul, hx2, enc6_enc.enc_one])
  obtain ⟨hc, hL4⟩ := h4 (by
    rw [← hev, ← enc6_enc.enc_mul, ← enc6_enc.enc_mul, hy4, enc6_enc.enc_one])
  have hrow0 : P.allN 136 (fun c => pairOK 360 E P (L2 (R2 iu)) (L4 c)
      (W (Nat.add (Nat.mul 136 (R2 iu)) c))) = true := WK.all _ hr
  have hrow := (P.allN_iff _ _).1 hrow0 _ hc
  rw [hL2, hL4] at hrow
  have hcases := pairOK_sound enc6_enc enc6_x enc6_y tree_ok hex θ.toMonoidHom xy_five xyy_five
    (hθ a6x) (hθ a6y) hne' hiu hiv heu.symm hev.symm hrow
  have e : ∀ z, θ.toMonoidHom z = θ z := fun _ => rfl
  simp only [InvCases, e] at hcases
  rcases hcases with ⟨g, h2, h4⟩ | ⟨a, b, g, ha3, hb3, ha1, hab, hb1, hba, hbaa, hcase, hw1, hw2⟩
  · left
    refine ⟨g, ?_⟩
    have h2' : ¬(θ g * g⁻¹) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      exact h2
    have h4' : (θ g * g⁻¹) ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
      exact h4
    rw [orderOf_eq_prime_pow h2' h4']
    norm_num
  · right
    have ha3' : a ^ 3 = 1 := by
      rw [pow_three']
      exact ha3
    have hb3' : b ^ 3 = 1 := by
      rw [pow_three']
      exact hb3
    have hainv : a * a = a⁻¹ := eq_inv_of_mul_eq_one_left ha3
    refine ⟨a, b, g, ha3', hb3', ha1, hab, ?_, ?_, ?_⟩
    · intro hmem
      rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime ha3' ha1] at hmem
      simp only [Finset.mem_image, Finset.mem_range] at hmem
      obtain ⟨k, hk, hkb⟩ := hmem
      interval_cases k
      · exact hb1 (by rw [← hkb, pow_zero])
      · exact hba (by rw [← hkb, pow_one])
      · exact hbaa (by rw [← hkb, pow_two])
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.trans hainv, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    · exact orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1

end CertificateChecks.KernelMisc.A6Aut

end
