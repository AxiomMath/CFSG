module

public import Certificates.Kernel.Hall82K.MLGlue
public import Certificates.Kernel.Hall82K.MR

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Hall82K CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.KC.Ord CFSG.KD.Hall82E CFSG.CGT.Hall82
open CFSG.KD.Hall82R CFSG.KD.Hall82A CFSG.ComponentClassification.AS81.Hexa
open CFSG.Monster.B.Co2

theorem cntK_succ (q : ℕ → Bool) (n : ℕ) :
    cntK q (n + 1) = cntK q n + (if q n = true then 1 else 0) := by
  change Nat.add (cntK q n) (Bool.rec 0 1 (q n)) = _
  cases q n <;> rfl

theorem cntK_eq (q : ℕ → Bool) : ∀ n, cntK q n = ((Finset.range n).filter fun i => q i = true).card
  | 0 => rfl
  | n + 1 => by
    rw [cntK_succ, cntK_eq q n, Finset.range_add_one, Finset.filter_insert]
    split
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

theorem natCard_eq_cntK {n : ℕ} (q : ℕ → Bool) (s : Set (Fin n))
    (hs : ∀ i : Fin n, i ∈ s ↔ q i.val = true) : Nat.card s = cntK q n := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight hs), Nat.card_eq_fintype_card,
    Fintype.card_subtype, cntK_eq]
  refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [Finset.mem_filter, hi]
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

theorem rm_bound (B : Subgroup (Equiv.Perm (Fin 64))) (hB : B ≤ hallRM) (hne : B ≠ ⊥) :
    Nat.card B * Nat.card (fixPts (B : Set (Equiv.Perm (Fin 64)))) ≤ 32 := by
  classical
  let p : ℕ → Bool := fun e => if h : e < 8 then decide (hallRMPerm ⟨e, h⟩ ∈ B) else false
  let m := maskOf p 8
  have hm : ∀ e : Fin 8, inM m e.val = true ↔ hallRMPerm e ∈ B := by
    intro e
    rw [inM_maskOf p e.2]
    simp [p, e.2]
  have hm' : ∀ e (he : e < 8), inM m e = true ↔ hallRMPerm ⟨e, he⟩ ∈ B := fun e he =>
    hm ⟨e, he⟩
  have hclosed : closed8K m = true := by
    refine (allN_iff _ _).2 fun e he => (allN_iff _ _).2 fun f hf => impB_of fun hef => ?_
    obtain ⟨hme, hmf⟩ := andB_eq_true hef
    have hx : Nat.xor e f < 8 := Nat.xor_lt_two_pow (n := 3) he hf
    rw [hm' _ hx]
    have h := B.mul_mem ((hm' e he).1 hme) ((hm' f hf).1 hmf)
    rw [rm_mul] at h
    exact h
  have hm1 : negK (Nat.beq m 1) = true := by
    cases h : Nat.beq m 1
    · rfl
    · exfalso
      have h1 : m = 1 := Nat.eq_of_beq_eq_true h
      refine hne (eq_bot_iff.2 fun x hx => ?_)
      obtain ⟨e, rfl⟩ := (mem_rm_iff x).1 (hB hx)
      have he := (hm e).2 hx
      rw [h1] at he
      have h8 : ∀ e : Fin 8, inM 1 e.val = true → e = 0 := by decide
      rw [Subgroup.mem_bot, h8 e he, rm_zero]
  have hchk := impB_eq_true ((allN_iff _ _).1 ch840001le32 m (maskOf_lt p 8))
    (andB_of hclosed hm1)
  have hcardB : Nat.card B = cntK (inM m) 8 := by
    have himg : (B : Set (Equiv.Perm (Fin 64))) = hallRMPerm '' {e | inM m e.val = true} := by
      ext x
      constructor
      · intro hx
        obtain ⟨e, rfl⟩ := (mem_rm_iff x).1 (hB hx)
        exact ⟨e, (hm e).2 hx, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact (hm e).1 he
    change Nat.card (B : Set (Equiv.Perm (Fin 64))) = _
    rw [himg, Nat.card_image_of_injective rm_inj]
    exact natCard_eq_cntK (inM m) _ fun _ => Iff.rfl
  have hcardF : Nat.card (fixPts (B : Set (Equiv.Perm (Fin 64)))) = cntK (fixMK RMP m) 64 := by
    refine natCard_eq_cntK _ _ fun v => ?_
    constructor
    · intro hv
      refine (allN_iff _ _).2 fun e he => impB_of fun hme => ?_
      have h := hv _ ((hm' e he).1 hme)
      have hval := rm_val ⟨e, he⟩ v
      rw [h] at hval
      rw [← hval]
      exact Nat.beq_refl _
    · intro hv b hb
      obtain ⟨e, rfl⟩ := (mem_rm_iff b).1 (hB hb)
      have h := impB_eq_true ((allN_iff _ _).1 hv e.val e.2) ((hm e).2 hb)
      exact Fin.ext ((rm_val e v).trans (Nat.eq_of_beq_eq_true h))
  rw [hcardB, hcardF]
  exact Nat.le_of_ble_eq_true hchk

theorem card_map_conjK (B : Subgroup (Equiv.Perm (Fin 64))) (m : Equiv.Perm (Fin 64)) :
    Nat.card (B.map (MulAut.conj m).toMonoidHom) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj m).injective

theorem fixPts_conj_imageK (S : Set (Equiv.Perm (Fin 64))) (m : Equiv.Perm (Fin 64)) :
    fixPts ((fun b => m * b * m⁻¹) '' S) = m '' fixPts S := by
  ext x
  simp only [fixPts, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro h
    refine ⟨m⁻¹ x, ?_, by simp⟩
    intro b hb
    have h2 := h (m * b * m⁻¹) ⟨b, hb, rfl⟩
    have h1 : (m * b * m⁻¹) x = m (b (m⁻¹ x)) := by simp [Equiv.Perm.mul_apply]
    rw [h1] at h2
    have h3 := congrArg (fun z => m⁻¹ z) h2
    simpa using h3
  · rintro ⟨y, hy, rfl⟩ b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have h1 : (m * b₀ * m⁻¹) (m y) = m (b₀ y) := by simp [Equiv.Perm.mul_apply]
    rw [h1, hy b₀ hb₀]

theorem coe_map_conjK (B : Subgroup (Equiv.Perm (Fin 64))) (m : Equiv.Perm (Fin 64)) :
    ((B.map (MulAut.conj m).toMonoidHom : Subgroup (Equiv.Perm (Fin 64))) : Set _) =
      (fun b => m * b * m⁻¹) '' (B : Set (Equiv.Perm (Fin 64))) := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_map, MulAut.conj_apply]
  constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩

theorem card_fixPts_map_conjK (B : Subgroup (Equiv.Perm (Fin 64))) (m : Equiv.Perm (Fin 64)) :
    Nat.card (fixPts ((B.map (MulAut.conj m).toMonoidHom : Subgroup (Equiv.Perm (Fin 64))) :
        Set (Equiv.Perm (Fin 64)))) = Nat.card (fixPts (B : Set (Equiv.Perm (Fin 64)))) := by
  rw [coe_map_conjK, fixPts_conj_imageK, Nat.card_image_of_injective m.injective]

theorem le_32 : ∀ (v : Fin 64) (X : Subgroup (Equiv.Perm (Fin 64))), X ≤ hexaM → IsPGroup 2 X →
    (∀ x ∈ X, x v = v) → (∀ a ∈ hexaL, a v = v → ∀ x ∈ X, a * x * a⁻¹ ∈ X) →
    ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ X → B ≠ ⊥ →
      Nat.card B * Nat.card (fixPts B) ≤ 32 := by
  intro v X hX h2 hfix hnorm B hBX hne
  by_cases hv0 : v = 0
  · subst hv0
    have hX0 := eq_bot X hX h2 fun a ha x hx => hnorm a ha (apply_zero (hexaL_le ha)) x hx
    exact absurd (eq_bot_iff.2 (hX0 ▸ hBX)) hne
  by_cases hvK : IsOvalVec v
  · have hX0 := eq_bot_of_oval v hvK X hX h2 hfix hnorm
    exact absurd (eq_bot_iff.2 (hX0 ▸ hBX)) hne
  obtain ⟨a, haL, ha5⟩ := five_trans v hv0 hvK
  let φ := MulAut.conj a⁻¹
  have hφ : ∀ y, φ y = a⁻¹ * y * a := fun y => by
    change a⁻¹ * y * a⁻¹⁻¹ = _
    rw [inv_inv]
  let X' := X.map φ.toMonoidHom
  let B' := B.map φ.toMonoidHom
  have hmemX' : ∀ y, y ∈ X' ↔ ∃ x ∈ X, a⁻¹ * x * a = y := by
    intro y
    simp only [X', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, hφ]
  have hX'M : X' ≤ hexaM := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmemX' y).1 hy
    exact hexaM.mul_mem (hexaM.mul_mem (hexaM.inv_mem (hexaL_le haL)) (hX hx)) (hexaL_le haL)
  have hX'2 : IsPGroup 2 X' := h2.map _
  have hX'5 : ∀ y ∈ X', y 5 = 5 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hmemX' y).1 hy
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha5, hfix x hx, ← ha5]
    simp
  have hX'n : ∀ c ∈ hexaL, c 5 = 5 → ∀ y ∈ X', c * y * c⁻¹ ∈ X' := by
    intro c hc hc5 y hy
    obtain ⟨x, hx, rfl⟩ := (hmemX' y).1 hy
    have hcL : a * c * a⁻¹ ∈ hexaL := hexaL.mul_mem (hexaL.mul_mem haL hc) (hexaL.inv_mem haL)
    have hcv : (a * c * a⁻¹) v = v := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← ha5]
      simp [hc5]
    refine (hmemX' _).2 ⟨_, hnorm _ hcL hcv x hx, ?_⟩
    group
  have hX'R := le_rm X' hX'M hX'2 hX'5 hX'n
  have hB'X' : B' ≤ X' := Subgroup.map_mono hBX
  have hB'ne : B' ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective B φ.injective).1 h)
  have hb := rm_bound B' (hB'X'.trans hX'R) hB'ne
  rw [card_map_conjK, card_fixPts_map_conjK] at hb
  exact hb

end CFSG.KD.Hall82L
