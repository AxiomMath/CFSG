module

public import Certificates.Kernel.HN1408.CayleyGlue
public import Certificates.Kernel.HN1408.ShIIDefs

public section

namespace CFSG.KD.HN1408

@[expose] def zEnc (n : Nat) (x : Multiplicative (ZMod n)) : Nat := (Multiplicative.toAdd x).val

theorem zEnc_lt (n : Nat) [NeZero n] (x : Multiplicative (ZMod n)) : zEnc n x < n :=
  ZMod.val_lt _

@[expose] def zCode (n : Nat) [NeZero n] : CodeM (Multiplicative (ZMod n)) where
  enc := zEnc n
  mulC := zMul n
  inj x y h := Multiplicative.toAdd.injective (ZMod.val_injective n h)
  hom x y := by
    unfold zEnc zMul
    rw [toAdd_mul, ZMod.val_add]

@[expose] def q8Enc : QuaternionGroup 2 → Nat
  | .a i => i.val
  | .xa i => 4 + i.val

@[expose] def q8Code : CodeM (QuaternionGroup 2) where
  enc := q8Enc
  mulC := q8Mul
  inj := by
    intro x y
    revert x y
    decide +kernel
  hom := by decide +kernel

@[expose] def d10Enc : DihedralGroup 5 → Nat
  | .r i => i.val
  | .sr i => 5 + i.val

@[expose] def d10Code : CodeM (DihedralGroup 5) where
  enc := d10Enc
  mulC := d10Mul
  inj := by
    intro x y
    revert x y
    decide +kernel
  hom := by decide +kernel

theorem mod_div_code {b x y : Nat} (hx : x < b) : (x + b * y) % b = x ∧ (x + b * y) / b = y := by
  have hb : 0 < b := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hx, Nat.zero_add]

@[expose] def prodCode {A B : Type} [Mul A] [Mul B] (M₁ : CodeM A) (M₂ : CodeM B) (b : Nat)
    (hb : ∀ x, M₁.enc x < b) : CodeM (A × B) where
  enc p := M₁.enc p.1 + b * M₂.enc p.2
  mulC := prodMul b M₁.mulC M₂.mulC
  inj p q h := by
    obtain ⟨p1, p2⟩ := mod_div_code (y := M₂.enc p.2) (hb p.1)
    obtain ⟨q1, q2⟩ := mod_div_code (y := M₂.enc q.2) (hb q.1)
    simp only [] at h
    rw [h] at p1 p2
    exact Prod.ext (M₁.inj (p1.symm.trans q1)) (M₂.inj (p2.symm.trans q2))
  hom p q := by
    obtain ⟨p1, p2⟩ := mod_div_code (y := M₂.enc p.2) (hb p.1)
    obtain ⟨q1, q2⟩ := mod_div_code (y := M₂.enc q.2) (hb q.1)
    unfold prodMul
    rw [p1, p2, q1, q2, Prod.fst_mul, Prod.snd_mul, M₁.hom, M₂.hom]

@[expose] def s5Code : CodeM (Multiplicative (ZMod 2) × QuaternionGroup 2) :=
  prodCode (zCode 2) q8Code 2 (zEnc_lt 2)

@[expose] def b5Code :
    CodeM (Multiplicative (ZMod 5) × Multiplicative (ZMod 2) × DihedralGroup 5) :=
  prodCode (zCode 5) (prodCode (zCode 2) d10Code 2 (zEnc_lt 2)) 5 (zEnc_lt 5)

end CFSG.KD.HN1408

end
