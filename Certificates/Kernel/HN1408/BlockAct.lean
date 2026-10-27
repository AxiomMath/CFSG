module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.KD.HN1408.BlockAct

open CFSG.EvenSporadicStandard.HNRecog.Section3

variable {X : Type*} [Group X] (φ : X →* Equiv.Perm (Fin 1408)) (lab : Fin 1408 → ℕ) (n : ℕ)
  (R : ℕ → Fin 1408)

structure IsBlocks : Prop where
  rep : ∀ k < n, lab (R k) = k + 1
  le : ∀ x, lab x ≤ n
  map : ∀ g : X, ∀ x, lab x ≠ 0 → lab (φ g x) ≠ 0 ∧ lab (φ g x) = lab (φ g (R (lab x - 1)))

variable {φ lab n R}

theorem lab_rep_ne (hb : IsBlocks φ lab n R) {k : ℕ} (hk : k < n) : lab (R k) ≠ 0 := by
  rw [hb.rep k hk]
  omega

theorem lab_map_ne (hb : IsBlocks φ lab n R) (g : X) {k : ℕ} (hk : k < n) :
    lab (φ g (R k)) ≠ 0 :=
  (hb.map g (R k) (lab_rep_ne hb hk)).1

@[expose] noncomputable def act (hb : IsBlocks φ lab n R) (g : X) (k : Fin n) : Fin n :=
  ⟨lab (φ g (R k)) - 1, by
    have h1 := hb.le (φ g (R k))
    have h2 := lab_map_ne hb g k.isLt
    omega⟩

theorem act_val (hb : IsBlocks φ lab n R) (g : X) (k : Fin n) :
    (act hb g k).val = lab (φ g (R k)) - 1 := rfl

theorem act_one (hb : IsBlocks φ lab n R) (k : Fin n) : act hb 1 k = k := by
  apply Fin.ext
  rw [act_val, map_one, Equiv.Perm.one_apply, hb.rep k k.isLt]
  omega

theorem act_mul (hb : IsBlocks φ lab n R) (g h : X) (k : Fin n) :
    act hb (g * h) k = act hb g (act hb h k) := by
  apply Fin.ext
  rw [act_val, act_val, act_val, map_mul, Equiv.Perm.mul_apply]
  have hx := lab_map_ne hb h k.isLt
  rw [(hb.map g _ hx).2]

@[expose] noncomputable def blockHom (hb : IsBlocks φ lab n R) : X →* Equiv.Perm (Fin n) where
  toFun g :=
    { toFun := act hb g
      invFun := act hb g⁻¹
      left_inv := fun k => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun k => by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := by
    ext k
    exact congrArg Fin.val (act_one hb k)
  map_mul' g h := by
    ext k
    exact congrArg Fin.val (act_mul hb g h k)

theorem blockHom_apply (hb : IsBlocks φ lab n R) (g : X) (k : Fin n) :
    blockHom hb g k = act hb g k := rfl

theorem blockHom_eq_one (hb : IsBlocks φ lab n R) {g : X} (h : blockHom hb g = 1) :
    ∀ k < n, lab (φ g (R k)) = k + 1 := by
  intro k hk
  have e := congrArg Fin.val (Equiv.ext_iff.1 h ⟨k, hk⟩)
  rw [blockHom_apply, act_val, Equiv.Perm.one_apply] at e
  have := lab_map_ne hb g hk
  change lab (φ g (R k)) - 1 = k at e
  omega

theorem natCard_perm_two : Nat.card (Equiv.Perm (Fin 2)) = 2 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem natCard_z_two : Nat.card (Z 2) = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem injective_of_blocks {lab' : Fin 1408 → ℕ} {R' : ℕ → Fin 1408}
    (hb : IsBlocks φ lab n R) (hs : IsBlocks φ lab' 2 R')
    (hker : ∀ g : X, (∀ k < n, lab (φ g (R k)) = k + 1) → (∀ k < 2, lab' (φ g (R' k)) = k + 1) →
      g = 1) :
    ∃ f : X →* Z 2 × Sym n, Function.Injective f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : Equiv.Perm (Fin 2) ≃* Z 2 := mulEquivOfPrimeCardEq natCard_perm_two natCard_z_two
  refine ⟨(e.toMonoidHom.comp (blockHom hs)).prod (blockHom hb), ?_⟩
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hg
  have h2 : blockHom hs g = 1 := by
    have := hg.1
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff e e.injective] at this
    exact this
  exact hker g (blockHom_eq_one hb hg.2) (blockHom_eq_one hs h2)

end CFSG.KD.HN1408.BlockAct

end
