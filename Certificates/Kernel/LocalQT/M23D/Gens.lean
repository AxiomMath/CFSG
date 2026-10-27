module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23DataInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11

public section

namespace CFSG.KD.LQT.M23D

open Equiv CFSG.QuasithinUnique.Vol2Native.L239.Covers CFSG.Sporadic.Schreier CFSG.Blueprint
open scoped Pointwise

@[expose] noncomputable def letN {α : Sort _} (y : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

theorem letN_eq {α : Sort _} (y : ℕ) (k : ℕ → α) : letN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def appK (l1 l2 : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) l2 (fun a _ ih => a :: ih) l1

theorem appK_eq (l1 l2 : List ℕ) : appK l1 l2 = l1 ++ l2 := by
  induction l1 with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

@[expose] noncomputable def allK {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => Bool.and (p a) ih) l

theorem allK_true {α : Type} (p : α → Bool) (l : List α) (h : allK p l = true) :
    ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h' : (p a && allK p l) = true := h
    rw [Bool.and_eq_true] at h'
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact ih h'.2 x hx

@[expose] noncomputable def isNilK (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

theorem isNilK_true {L : List ℕ} (h : isNilK L = true) : L = [] := by
  cases L with
  | nil => rfl
  | cons _ _ => exact absurd h Bool.false_ne_true

@[expose] def fA : Fin 23 → Fin 23 :=
  ![1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def fB : Fin 23 → Fin 23 :=
  ![15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def fBi : Fin 23 → Fin 23 :=
  ![2, 11, 10, 22, 3, 17, 6, 4, 1, 9, 15, 20, 19, 21, 16, 0, 14, 13, 18, 12, 8, 5, 7]

theorem fA_fA : ∀ x, fA (fA x) = x := by decide +kernel

theorem fB_fBi : ∀ x, fB (fBi x) = x := by decide +kernel

theorem fBi_fB : ∀ x, fBi (fB x) = x := by decide +kernel

@[expose] def pA : Perm (Fin 23) := ⟨fA, fA, fA_fA, fA_fA⟩

@[expose] def pBi : Perm (Fin 23) := ⟨fBi, fB, fB_fBi, fBi_fB⟩

@[expose] def gP : Fin 2 → Perm (Fin 23) := ![pA, pBi]

theorem gM0_link : ∀ i, ((gM 0 : M23g) : Perm (Fin 23)) i = pA i := by decide +kernel

theorem gM1_link : ∀ i, ((gM 1 : M23g) : Perm (Fin 23)) i = pBi i := by decide +kernel

@[expose] def aP : Perm (Fin 23) := wordVal gP alphaW

@[expose] def bP : Perm (Fin 23) := wordVal gP betaW

theorem relP1 : wordVal ![aP, bP] m11R1 = 1 := by decide +kernel

theorem relP2 : wordVal ![aP, bP] m11R2 = 1 := by decide +kernel

theorem aP_ne_one : aP ≠ 1 := by decide +kernel

theorem aP_fix : D23.image aP = D23 := by decide +kernel

theorem bP_fix : D23.image bP = D23 := by decide +kernel

theorem gP_eq : (fun i => ((gM i : M23g) : Perm (Fin 23))) = gP := by
  funext i
  fin_cases i
  · exact Equiv.ext gM0_link
  · exact Equiv.ext gM1_link

theorem coe_wordVal (w : List Letter) :
    ((wordVal gM w : M23g) : Perm (Fin 23)) = wordVal gP w :=
  (map_wordVal (NativeSporadic.M23).subtype gM w).trans (congrArg (wordVal · w) gP_eq)

theorem coe_letterVal (l : Letter) :
    ((letterVal gM l : M23g) : Perm (Fin 23)) = letterVal gP l :=
  (map_letterVal (NativeSporadic.M23).subtype gM l).trans (congrArg (letterVal · l) gP_eq)

theorem coe_alphaG : ((alphaG : M23g) : Perm (Fin 23)) = aP := coe_wordVal alphaW

theorem coe_betaG : ((betaG : M23g) : Perm (Fin 23)) = bP := coe_wordVal betaW

theorem coe_yM : (fun i => ((yM i : M23g) : Perm (Fin 23))) = ![aP, bP] := by
  funext i
  fin_cases i
  · exact coe_alphaG
  · exact coe_betaG

theorem smul_eq_image (g : M23g) (t : Finset (Fin 23)) :
    g • t = t.image fun x => (g : Perm (Fin 23)) x := by
  rw [Finset.smul_finset_def]
  rfl

theorem yM_rel1 : wordVal yM m11R1 = 1 :=
  Subtype.ext ((map_wordVal (NativeSporadic.M23).subtype yM m11R1).trans
    ((congrArg (wordVal · m11R1) coe_yM).trans relP1))

theorem yM_rel2 : wordVal yM m11R2 = 1 :=
  Subtype.ext ((map_wordVal (NativeSporadic.M23).subtype yM m11R2).trans
    ((congrArg (wordVal · m11R2) coe_yM).trans relP2))

theorem yM_ne_one : yM 0 ≠ 1 := fun h =>
  aP_ne_one (coe_alphaG.symm.trans (congrArg Subtype.val h))

theorem alphaG_fix : alphaG • D23 = D23 := by
  rw [smul_eq_image, coe_alphaG]
  exact aP_fix

theorem betaG_fix : betaG • D23 = D23 := by
  rw [smul_eq_image, coe_betaG]
  exact bP_fix

@[expose] def enc (t : Finset (Fin 23)) : ℕ := ∑ i ∈ t, 2 ^ (i : ℕ)

@[expose] noncomputable def img (c i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 5) i)) (nat_lit 31)

@[expose] noncomputable def pmR (c m n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun i acc => Nat.add acc
      (Nat.shiftLeft (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (img c i))) n

@[expose] noncomputable def pm (c m : ℕ) : ℕ := letN m fun m => pmR c m (nat_lit 23)

@[expose] def cA : ℕ := 29396287020561317414859794500619265

@[expose] def cBi : ℕ := 9299982975027872919014373496400226

@[expose] def cB : ℕ := 4436007312844787929641103698034959

@[expose] noncomputable def codeL (i : Fin 2) (b : Bool) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) cA cB (Nat.beq i.val 1))
    (Bool.rec (motive := fun _ => ℕ) cA cBi (Nat.beq i.val 1)) b

theorem codeL_ok : ∀ (i : Fin 2) (b : Bool) (x : Fin 23),
    (letterVal gP (i, b) x : ℕ) = img (codeL i b) x := by
  decide +kernel

theorem enc_eq_sum_map (t : Finset (Fin 23)) :
    enc t = ∑ j ∈ t.map Fin.valEmbedding, 2 ^ j := by
  rw [Finset.sum_map]
  rfl

theorem enc_injective : Function.Injective enc := by
  intro s t h
  rw [enc_eq_sum_map, enc_eq_sum_map] at h
  exact Finset.map_injective Fin.valEmbedding (Finset.geomSum_injective le_rfl h)

theorem testBit_enc (t : Finset (Fin 23)) (i : ℕ) :
    (enc t).testBit i ↔ ∃ x ∈ t, (x : ℕ) = i := by
  rw [enc_eq_sum_map, ← Nat.mem_bitIndices, ← List.mem_toFinset,
    Finset.toFinset_bitIndices_sum_two_pow]
  simp

theorem land_shiftRight_one (m i : ℕ) :
    Nat.land (Nat.shiftRight m i) 1 = if m.testBit i then 1 else 0 := by
  change (m >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> simp [h]

theorem pmR_eq_sum (c m n : ℕ) :
    pmR c m n = ∑ i ∈ Finset.range n,
      Nat.shiftLeft (Nat.land (Nat.shiftRight m i) 1) (img c i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem pm_enc {c : ℕ} {σ : Perm (Fin 23)} (h : ∀ x : Fin 23, (σ x : ℕ) = img c x)
    (t : Finset (Fin 23)) : pm c (enc t) = enc (t.image σ) := by
  have hr : enc (t.image σ) = ∑ x ∈ t, 2 ^ (σ x : ℕ) :=
    Finset.sum_image (fun x _ y _ hxy => σ.injective hxy)
  rw [pm, letN_eq, pmR_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => Nat.shiftLeft (Nat.land (Nat.shiftRight (enc t) i) 1)
      (img c i)) 23, hr]
  have hx : ∀ x : Fin 23, Nat.shiftLeft (Nat.land (Nat.shiftRight (enc t) x) 1) (img c x) =
      if x ∈ t then 2 ^ (σ x : ℕ) else 0 := by
    intro x
    rw [land_shiftRight_one, ← h x]
    by_cases hx : x ∈ t
    · have hb : (enc t).testBit x := (testBit_enc t x).2 ⟨x, hx, rfl⟩
      simp only [hb, hx, ↓reduceIte]
      exact Nat.one_shiftLeft _
    · have hb : ¬ (enc t).testBit x := fun hb => by
        obtain ⟨y, hy, hyx⟩ := (testBit_enc t x).1 hb
        exact hx (Fin.ext hyx ▸ hy)
      simp only [hb, hx, ↓reduceIte]
      exact Nat.zero_shiftLeft _
  simp_rw [hx]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem pm_letter (i : Fin 2) (b : Bool) (t : Finset (Fin 23)) :
    pm (codeL i b) (enc t) = enc (letterVal gM (i, b) • t) := by
  rw [smul_eq_image, coe_letterVal]
  exact pm_enc (codeL_ok i b) t

end CFSG.KD.LQT.M23D
