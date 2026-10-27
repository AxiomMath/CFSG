module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.Rels
public import Certificates.Kernel.M24.Words
public import CFSG.Certificates.Kernel.DceSPDec
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CertificateChecks.KernelBounds.HNW

open CFSG.KC.HNA CFSG.KC.HNA.DceS CFSG.Certificates CFSG.KM24.Words

theorem byte_eq (w i : ℕ) : byte w i = w / 2 ^ (8 * i) % 256 := by
  change Nat.land (w >>> (8 * i)) 255 = _
  rw [land_255, Nat.shiftRight_eq_div_pow]

theorem letCode_lt (p : ℕ × Bool) : letCode p < 256 := by
  obtain ⟨g, b⟩ := p
  change Nat.land _ 255 < 256
  rw [land_255]
  exact Nat.mod_lt _ (by norm_num)

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

theorem byte_encW : ∀ (w : List (ℕ × Bool)) (i : ℕ) (hi : i < w.length),
    byte (encW w).1 i = letCode (w[i]'hi)
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | x :: w, 0, _ => byte_cons0 _ _ (letCode_lt x)
  | x :: w, i + 1, hi => by
    change byte (Nat.lor (letCode x) (Nat.shiftLeft (encW w).1 8)) (i + 1) = _
    rw [byte_consS _ _ _ (letCode_lt x)]
    exact byte_encW w i (by simpa using hi)

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

theorem rval_encEnt {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) (hl : w.length < 1024) :
    DSP.rval x (encEnt w) = (w.map fun p => x (letCode p)).prod := by
  rw [DSP.rval, bits_encEnt w hl, shift_encEnt w hl]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [byte_encW w i (by simpa using h1)]

theorem nOnly_encEnt (TL VL NL : ℕ) (w : List (ℕ × Bool)) (hl : w.length < 1024)
    (h : ∀ p ∈ w, isN TL VL NL (letCode p) = true) : DSP.nOnly TL VL NL (encEnt w) := by
  intro i hi
  rw [bits_encEnt w hl] at hi
  rw [shift_encEnt w hl, byte_encW w i hi]
  exact h _ (List.getElem_mem hi)

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

end CertificateChecks.KernelBounds.HNW

end
