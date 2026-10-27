module

public import CFSG.Certificates.Kernel.Fi22.Fix.Defs
public import CFSG.Certificates.Kernel.HOrbSound
public import Certificates.Kernel.Co2.Words
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22F CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

@[expose] noncomputable def innerB (m : ℕ) (f : ℕ → Bool) (h : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun l ih2 => Bool.rec (motive := fun _ => Bool) false ih2
    ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m)) (Nat.add (Nat.shiftLeft h 6) l))) 64

theorem allBelow_succ (m n : ℕ) (f : ℕ → Bool) :
    allBelow m (n + 1) f = Bool.rec (motive := fun _ => Bool) false (allBelow m n f) (innerB m f n) := rfl

theorem brec_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp)
  · exact ⟨rfl, h⟩

theorem inner_spec {m : ℕ} {f : ℕ → Bool} {h : ℕ} (hh : innerB m f h = true) :
    ∀ l < 64, Nat.add (Nat.shiftLeft h 6) l < m → f (Nat.add (Nat.shiftLeft h 6) l) = true := by
  have key : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun l ih2 => Bool.rec (motive := fun _ => Bool) false ih2
      ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m)) (Nat.add (Nat.shiftLeft h 6) l))) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft h 6) l < m → f (Nat.add (Nat.shiftLeft h 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hm
      obtain ⟨h1, h2⟩ := brec_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact ih h2 l hl hm
      · have hb : Nat.blt (Nat.add (Nat.shiftLeft h 6) l) m = true := by simpa using hm
        have h1' : Bool.rec (motive := fun _ => Bool) true (f (Nat.add (Nat.shiftLeft h 6) l))
            (Nat.blt (Nat.add (Nat.shiftLeft h 6) l) m) = true := h1
        rw [hb] at h1'
        exact h1'
  exact key 64 hh

theorem allBelow_spec {m : ℕ} {f : ℕ → Bool} :
    ∀ hi, allBelow m hi f = true → ∀ i < m, i < 64 * hi → f i = true := by
  intro hi
  induction hi with
  | zero => intro _ i _ h; omega
  | succ n ih =>
    intro h i him hin
    rw [allBelow_succ] at h
    obtain ⟨h1, h2⟩ := brec_true h
    by_cases hlt : i < 64 * n
    · exact ih h2 i him hlt
    · have e : i = Nat.add (Nat.shiftLeft n 6) (i - 64 * n) := by
        rw [show Nat.shiftLeft n 6 = n * 2 ^ 6 from Nat.shiftLeft_eq n 6]
        simp only [Nat.add_eq]
        omega
      rw [e] at him ⊢
      exact inner_spec h1 (i - 64 * n) (by omega) him

theorem nP_lt : nP < 64 * 55 := by decide

theorem every {f : ℕ → Bool} (h : allBelow nP (nat_lit 55) f = true) : ∀ i < nP, f i = true :=
  fun i hi => allBelow_spec 55 h i hi (by have := nP_lt; omega)

variable {G : Type*} [Group G]

@[expose] def Acts (H : Subgroup G) (rep : ℕ → G) (LV Q : ℕ) (x : G) : Prop :=
  ∀ i < nP, pf Q i < nP ∧ rep (lv LV i) * x * (rep (lv LV (pf Q i)))⁻¹ ∈ H

theorem acts_id {H : Subgroup G} {rep : ℕ → G} {LV Q : ℕ} (h : idOK Q = true) : Acts H rep LV Q 1 := by
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every h i hi)
  rw [e, mul_one, mul_inv_cancel]
  exact ⟨hi, H.one_mem⟩

theorem acts_comp {H : Subgroup G} {rep : ℕ → G} {LV Q R Q' : ℕ} {x y : G} (h1 : Acts H rep LV Q x)
    (h2 : Acts H rep LV R y) (hc : compOK Q R Q' = true) : Acts H rep LV Q' (x * y) := by
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hc i hi)
  obtain ⟨r1, m1⟩ := h1 i hi
  obtain ⟨r2, m2⟩ := h2 (pf Q i) r1
  rw [e]
  refine ⟨r2, ?_⟩
  have := H.mul_mem m1 m2
  simpa [mul_assoc] using this

theorem chainOK_succ (Qs base : ℕ → ℕ) (k0 c : ℕ) :
    chainOK Qs base k0 (c + 1) =
      andB (chainOK Qs base k0 c) (compOK (Qs (Nat.add k0 c)) (base (Nat.add k0 c)) (Qs (Nat.succ (Nat.add k0 c)))) :=
  rfl

theorem chain_acts {H : Subgroup G} {rep : ℕ → G} {LV : ℕ} {Qs base : ℕ → ℕ} {val pre : ℕ → G}
    {k0 cnt : ℕ} (hch : chainOK Qs base k0 cnt = true)
    (hb : ∀ k, k0 ≤ k → k < k0 + cnt → Acts H rep LV (base k) (val k))
    (hpre : ∀ k, k0 ≤ k → k < k0 + cnt → pre (k + 1) = pre k * val k)
    (h0 : Acts H rep LV (Qs k0) (pre k0)) : Acts H rep LV (Qs (k0 + cnt)) (pre (k0 + cnt)) := by
  induction cnt with
  | zero => simpa using h0
  | succ c ih =>
    rw [chainOK_succ] at hch
    obtain ⟨h1, h2⟩ := KB.andB_true hch
    have a := ih h1 (fun k hk hk' => hb k hk (by omega)) (fun k hk hk' => hpre k hk (by omega))
    have a' := acts_comp a (hb (k0 + c) (by omega) (by omega)) h2
    rw [← hpre (k0 + c) (by omega) (by omega)] at a'
    simpa [Nat.add_assoc] using a'

theorem lv_lt (LV i : ℕ) : lv LV i < 2 ^ 20 := by
  have : lv LV i ≤ 65535 := Nat.and_le_right
  omega

theorem bval_letW (gen : ℕ → G) {c : ℕ} (hc : c < 4) : bval gen (wWord (letW c)) (wLen (letW c)) = letV gen c := by
  unfold letW
  rw [HO.bval_withSent]
  have h1 : wWord (Nat.add 4 (Nat.shiftLeft c 12)) = c := by
    change (4 + c <<< 12) >>> 12 = c
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  have h2 : wLen (Nat.add 4 (Nat.shiftLeft c 12)) = 1 := by
    change ((4 + c <<< 12) >>> 2) &&& 1023 = 1
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [h1, h2, bval_succ, show bval gen (c / 256) 0 = 1 from rfl, mul_one, wLet_eq]
  congr 1
  omega

theorem acts_let {H : Subgroup G} {rep : ℕ → G} (gen : ℕ → G) {blk : ℕ → ℕ} {nf LV L Rs c : ℕ}
    (hwalk : ∀ w x R y, x < 2 ^ 20 → walkTo blk nf w x R y = true →
      rep x * bval gen (wWord w) (wLen w) * (rep y)⁻¹ ∈ H)
    (hc : c < 4) (hl : letOK blk nf LV L Rs c = true) (hr : rangeOK L = true) :
    Acts H rep LV L (letV gen c) := by
  intro i hi
  refine ⟨by simpa using every hr i hi, ?_⟩
  have := hwalk _ _ _ _ (lv_lt LV i) (every hl i hi)
  rwa [bval_letW gen hc] at this

end CertificateChecks.KernelFi22

end
