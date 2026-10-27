module

public import Certificates.Kernel.Misc.GL52.ClassEq
public import CFSG.Certificates.Kernel.Misc.GL52MatSound
public import CFSG.Literature.GL52Basic

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.KC.Ord CFSG.Literature.GL52 CFSG.GH74.KGroups

theorem listBeq_iff : ∀ a b : List ℕ, listBeq a b = true ↔ a = b := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons y ys => exact ⟨fun h => absurd h (by simp [listBeq]), fun h => absurd h (by simp)⟩
  | cons x xs ih =>
    intro b
    cases b with
    | nil => exact ⟨fun h => absurd h (by simp [listBeq]), fun h => absurd h (by simp)⟩
    | cons y ys =>
      change andB (Nat.beq x y) (listBeq xs ys) = true ↔ _
      rw [CFSG.KC.Misc.KG.andB_iff, CFSG.KC.Misc.KG.beq_true_iff, ih ys, List.cons.injEq]

theorem solCnt_eq (ps : List (Mat × Mat)) {P : List (ℕ × ℕ)} {L : List ℕ} {n : ℕ}
    (hP : ps.map (fun p => (mcode p.1, mcode p.2)) = P)
    (hE : listBeq (elimK P (25 * P.length) 25).2 L = true) (hC : unitCntK L = n) :
    Nat.card {g : G // ∀ p ∈ ps, (g : Mat) * p.1 = p.2 * (g : Mat)} = n := by
  have hl : ps.length = P.length := by rw [← hP, List.length_map]
  rw [solCnt_sound, hP, hl, (listBeq_iff _ _).1 hE, hC]

theorem unitCntR_chunks (L : List ℕ) (s : ℕ) :
    ∀ parts : List ℕ, ∀ lo, (∀ c < parts.length, unitCntR L (lo + c * s) s = parts.getD c 0) →
      unitCntR L lo (parts.length * s) = parts.sum := by
  intro parts
  induction parts with
  | nil =>
    intro lo _
    simp only [List.length_nil, Nat.zero_mul, List.sum_nil]
    rfl
  | cons x xs ih =>
    intro lo h
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm (xs.length * s) s, unitCntR_add,
      List.sum_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.zero_mul, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, ih (lo + s) fun c hc => by
      have := h (c + 1) (by simp; omega)
      rw [List.getD_cons_succ] at this
      have e : lo + s + c * s = lo + (c + 1) * s := by ring
      rw [e]
      exact this]

theorem coe_conj (g x : G) : ((g * x * g⁻¹ : G) : Mat) = (g : Mat) * x * ((g⁻¹ : G) : Mat) := by
  simp [Units.val_mul]

theorem isUnit_det_coe (g : G) : IsUnit (g : Mat).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

theorem rank_conj (g : G) (M : Mat) :
    ((g : Mat) * M * ((g⁻¹ : G) : Mat)).rank = M.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_coe g⁻¹),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_coe g)]

theorem inv_mul_coe (g : G) : ((g⁻¹ : G) : Mat) * (g : Mat) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem mul_inv_coe (g : G) : (g : Mat) * ((g⁻¹ : G) : Mat) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem peval_conj (g : G) (A : Mat) (cs : List (ZMod 2)) :
    peval ((g : Mat) * A * ((g⁻¹ : G) : Mat)) cs = (g : Mat) * peval A cs * ((g⁻¹ : G) : Mat) := by
  induction cs with
  | nil => simp [peval]
  | cons c cs ih =>
    change (peval ((g : Mat) * A * ((g⁻¹ : G) : Mat)) cs) * ((g : Mat) * A * ((g⁻¹ : G) : Mat)) +
      c • 1 = (g : Mat) * (peval A cs * A + c • 1) * ((g⁻¹ : G) : Mat)
    rw [ih]
    have e : (g : Mat) * peval A cs * ((g⁻¹ : G) : Mat) * ((g : Mat) * A * ((g⁻¹ : G) : Mat)) =
        (g : Mat) * (peval A cs * A) * ((g⁻¹ : G) : Mat) := by
      rw [Matrix.mul_assoc ((g : Mat) * peval A cs), ← Matrix.mul_assoc ((g⁻¹ : G) : Mat),
        ← Matrix.mul_assoc ((g⁻¹ : G) : Mat), inv_mul_coe, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      mul_inv_coe]

theorem invS_conj (g x : G) : invS ((g * x * g⁻¹ : G) : Mat) = invS (x : Mat) := by
  have key : ∀ k, (Nat.rec (motive := fun _ => ℕ) 0
      (fun m acc => acc * 8 + (peval ((g * x * g⁻¹ : G) : Mat) ((polyBits (m + 1)).map bitZ)).rank)
      k : ℕ) = Nat.rec (motive := fun _ => ℕ) 0
      (fun m acc => acc * 8 + (peval (x : Mat) ((polyBits (m + 1)).map bitZ)).rank) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change _ * 8 + _ = _ * 8 + _
      rw [ih, coe_conj, peval_conj, rank_conj]
  exact key 63

theorem sub_one_eq (A : Mat) : A - 1 = A + 1 := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem commDim_conj (g x : G) : commDim (g * x * g⁻¹) = commDim x := by
  rw [commDim, commDim, coe_conj]
  have e : (g : Mat) * x * ((g⁻¹ : G) : Mat) - 1 = (g : Mat) * ((x : Mat) - 1) * ((g⁻¹ : G) : Mat) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_inv_coe]
  rw [e, rank_conj]

theorem fixCount_eq (x : G) : fixCount x = 2 ^ (5 - ((x : Mat) + 1).rank) - 1 := by
  have h := two_pow_commDim x
  rw [commDim, sub_one_eq] at h
  omega

theorem fixCount_conj (g x : G) : fixCount (g * x * g⁻¹) = fixCount x := by
  have h1 := two_pow_commDim (g * x * g⁻¹)
  have h2 := two_pow_commDim x
  rw [commDim_conj] at h1
  omega

theorem rank_add_one (x : G) : ((x : Mat) + 1).rank = rankK (Nat.xor (mcode (x : Mat)) idK) := by
  rw [← mcode_one, mcode_add, rankK_mcode]

theorem card_exists_split {X : Type*} [Finite X] {α : Type*} (p : X → α → Prop)
    (hp : ∀ x a b, p x a → p x b → a = b) (Y : X → Prop) :
    ∀ R : List α, R.Nodup →
      Nat.card {x // (∃ a ∈ R, p x a) ∧ Y x} = (R.map fun a => Nat.card {x // p x a ∧ Y x}).sum := by
  intro R
  induction R with
  | nil => intro _; simp
  | cons a R ih =>
    intro hR
    rw [List.nodup_cons] at hR
    rw [List.map_cons, List.sum_cons, ← ih hR.2]
    have hs : ({x | (∃ b ∈ a :: R, p x b) ∧ Y x} : Set X) =
        {x | p x a ∧ Y x} ∪ {x | (∃ b ∈ R, p x b) ∧ Y x} := by
      ext x
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨⟨b, rfl | hb, hx⟩, hy⟩
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr ⟨⟨b, hb, hx⟩, hy⟩
      · rintro (⟨hx, hy⟩ | ⟨⟨b, hb, hx⟩, hy⟩)
        · exact ⟨⟨a, Or.inl rfl, hx⟩, hy⟩
        · exact ⟨⟨b, Or.inr hb, hx⟩, hy⟩
    have hd : Disjoint ({x | p x a ∧ Y x} : Set X) {x | (∃ b ∈ R, p x b) ∧ Y x} := by
      rw [Set.disjoint_left]
      rintro x ⟨hx, -⟩ ⟨⟨b, hb, hx'⟩, -⟩
      exact hR.1 (hp x a b hx hx' ▸ hb)
    have e1 : Nat.card {x // (∃ b ∈ a :: R, p x b) ∧ Y x} =
        ({x | (∃ b ∈ a :: R, p x b) ∧ Y x} : Set X).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card {x // p x a ∧ Y x} = ({x | p x a ∧ Y x} : Set X).ncard :=
      Nat.card_coe_set_eq _
    have e3 : Nat.card {x // (∃ b ∈ R, p x b) ∧ Y x} =
        ({x | (∃ b ∈ R, p x b) ∧ Y x} : Set X).ncard := Nat.card_coe_set_eq _
    rw [e1, e2, e3, hs, Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]

theorem conj_unique {A : G} {g a b : G} (ha : g * A = a * g) (hb : g * A = b * g) : a = b :=
  mul_right_cancel (ha.symm.trans hb)

theorem card_exists_pairs (A B : G) (R : List G) (hR : R.Nodup) :
    Nat.card {g : G // (∃ r ∈ R, g * A = r * g) ∧ ∃ r ∈ R, g * B = r * g} =
      (R.map fun a => (R.map fun b => Nat.card {g : G // g * A = a * g ∧ g * B = b * g}).sum).sum := by
  rw [card_exists_split (fun g a => g * A = a * g) (fun g a b ha hb => conj_unique ha hb) _ R hR]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  have e : Nat.card {g : G // g * A = a * g ∧ ∃ r ∈ R, g * B = r * g} =
      Nat.card {g : G // (∃ r ∈ R, g * B = r * g) ∧ g * A = a * g} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => and_comm)
  rw [e, card_exists_split (fun g b => g * B = b * g) (fun g a b ha hb => conj_unique ha hb) _ R hR]
  congr 1
  exact List.map_congr_left fun b _ =>
    Nat.card_congr (Equiv.subtypeEquivRight fun g => and_comm)

theorem filter_map_sum {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x
    · simp [h, ih]
    · simp [h, ih]

end CertificateChecks.KernelMisc.GL52K

end
