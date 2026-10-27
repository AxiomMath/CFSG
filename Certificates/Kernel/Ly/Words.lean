module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.Rels
public import CFSG.Certificates.Kernel.DceS5Dec
public import CFSG.Open.LocalVocabulary
public import Certificates.Kernel.M24.Words

public section

namespace CertificateChecks.KernelBounds.LyW

open CFSG.KC.LyA CFSG.KC.LyA.DceS CFSG.Certificates CFSG.KM24.Words

theorem byte_eq (w i : ℕ) : byte w i = w / 2 ^ (8 * i) % 256 := by
  change Nat.land (w >>> (8 * i)) 255 = _
  rw [land_255, Nat.shiftRight_eq_div_pow]

theorem letCode_eq (g : ℕ) (b : Bool) : letCode (g, b) = 2 * g + Bool.rec 1 0 b := by
  cases b <;> rfl

theorem letCode_lt (p : ℕ × Bool) (hp : p.1 < 128) : letCode p < 256 := by
  obtain ⟨g, b⟩ := p
  rw [letCode_eq]
  simp only at hp
  cases b <;> simp <;> omega

theorem byte_cons0 (c v : ℕ) (hc : c < 256) : byte (Nat.lor c (Nat.shiftLeft v 8)) 0 = c := by
  rw [lor_shift c v 8 (by simpa using hc), byte_eq, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
    show (2 : ℕ) ^ 8 = 256 by norm_num, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc]

theorem byte_consS (c v i : ℕ) (hc : c < 256) :
    byte (Nat.lor c (Nat.shiftLeft v 8)) (i + 1) = byte v i := by
  have e : (v * 2 ^ 8 + c) / 2 ^ 8 = v := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (by simpa using hc), Nat.zero_add]
  rw [lor_shift c v 8 (by simpa using hc), byte_eq, byte_eq, show 8 * (i + 1) = 8 + 8 * i by ring,
    Nat.pow_add, ← Nat.div_div_eq_div_mul, e]

theorem encW_len : ∀ w : List (ℕ × Bool), (encW w).2 = w.length
  | [] => rfl
  | x :: w => by
    change (encW w).2 + 1 = w.length + 1
    rw [encW_len w]

theorem byte_encW : ∀ (w : List (ℕ × Bool)), (∀ p ∈ w, p.1 < 128) → ∀ (i : ℕ) (hi : i < w.length),
    byte (encW w).1 i = letCode (w[i]'hi)
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | x :: w, hw, 0, _ => byte_cons0 _ _ (letCode_lt x (hw x List.mem_cons_self))
  | x :: w, hw, i + 1, hi => by
    change byte (Nat.lor (letCode x) (Nat.shiftLeft (encW w).1 8)) (i + 1) = _
    rw [byte_consS _ _ _ (letCode_lt x (hw x List.mem_cons_self))]
    exact byte_encW w (fun p hp => hw p (List.mem_cons_of_mem _ hp)) i (by simpa using hi)

theorem encEnt_eq (w : List (ℕ × Bool)) : encEnt w = (encW w).1 * 4096 + 4 * w.length := by
  change 4 * (encW w).2 + (encW w).1 <<< 12 = _
  rw [encW_len, Nat.shiftLeft_eq]
  ring

theorem bits_encEnt (w : List (ℕ × Bool)) (hl : w.length < 1024) :
    bits (encEnt w) 2 10 = w.length := by
  change ((encEnt w) >>> 2) &&& (2 ^ 10 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, encEnt_eq]
  have : ((encW w).1 * 4096 + 4 * w.length) / 2 ^ 2 = (encW w).1 * 1024 + w.length := by
    rw [show (encW w).1 * 4096 + 4 * w.length = ((encW w).1 * 1024 + w.length) * 2 ^ 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [this, show (2 : ℕ) ^ 10 = 1024 by norm_num, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hl]

theorem shift_encEnt (w : List (ℕ × Bool)) (hl : w.length < 1024) :
    Nat.shiftRight (encEnt w) 12 = (encW w).1 := by
  change (encEnt w) >>> 12 = _
  rw [Nat.shiftRight_eq_div_pow, encEnt_eq, Nat.add_comm, show (2 : ℕ) ^ 12 = 4096 by norm_num,
    Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem rval_encEnt {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) (hl : w.length < 1024)
    (hw : ∀ p ∈ w, p.1 < 128) : DS5.rval x (encEnt w) = (w.map fun p => x (letCode p)).prod := by
  rw [DS5.rval, bits_encEnt w hl, shift_encEnt w hl]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [byte_encW w hw i (by simpa using h1)]

theorem nOnly_encEnt (TL VL NL : ℕ) (w : List (ℕ × Bool)) (hl : w.length < 1024)
    (hw : ∀ p ∈ w, p.1 < 128) (h : ∀ p ∈ w, isN TL VL NL (letCode p) = true) :
    DS5.nOnly TL VL NL (encEnt w) := by
  intro i hi
  rw [bits_encEnt w hl] at hi
  rw [shift_encEnt w hl, byte_encW w hw i hi]
  exact h _ (List.getElem_mem hi)

@[expose] noncomputable def smallB (L : List (List (ℕ × Bool))) (G : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => CFSG.KM24.mAnd
    (CFSG.KM24.mAnd (Nat.blt (List.rec (motive := fun _ => Nat) 0 (fun _ _ n => Nat.succ n) w) 1024)
      (List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => CFSG.KM24.mAnd
          (Nat.blt (Prod.rec (motive := fun _ => Nat) (fun g _ => g) x) G) ih2)
        w)) ih) L

theorem letsLt (G : ℕ) : ∀ w : List (ℕ × Bool), List.rec (motive := fun _ => Bool) true
    (fun x _ ih2 => CFSG.KM24.mAnd (Nat.blt (Prod.rec (motive := fun _ => Nat) (fun g _ => g) x) G)
      ih2) w = true → ∀ x ∈ w, x.1 < G
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: w, h, x, hx => by
    obtain ⟨hy, hw⟩ := mAnd_eq_true h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.blt_eq.mp hy
    · exact letsLt G w hw x hx

theorem smallB_spec (G : ℕ) : ∀ L : List (List (ℕ × Bool)), smallB L G = true →
    ∀ w ∈ L, w.length < 1024 ∧ ∀ x ∈ w, x.1 < G
  | [], _, w, hw => absurd hw List.not_mem_nil
  | v :: L, h, w, hw => by
    obtain ⟨hv, hL⟩ := mAnd_eq_true h
    rcases List.mem_cons.mp hw with rfl | hw
    · obtain ⟨hlen, hlet⟩ := mAnd_eq_true hv
      exact ⟨by rw [← lenRec]; exact Nat.blt_eq.mp hlen, letsLt G w hlet⟩
    · exact smallB_spec G L hL w hw

theorem eqL_eq : ∀ (A B : List ℕ), eqL A B = true → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqL])
  | _ :: _, [], h => absurd h (by simp [eqL])
  | a :: A, b :: B, h => by
    change Bool.rec (motive := fun _ => Bool) false (eqL A B) (Nat.beq a b) = true at h
    cases hab : Nat.beq a b
    · rw [hab] at h
      exact absurd h (by simp)
    · rw [hab] at h
      rw [Nat.beq_eq] at hab
      rw [hab, eqL_eq A B h]

theorem encList_eq : ∀ L : List (List (ℕ × Bool)), encList L = L.map encEnt
  | [] => rfl
  | w :: L => by
    change encEnt w :: encList L = _
    rw [encList_eq L, List.map_cons]

end CertificateChecks.KernelBounds.LyW

end
