module

public import Certificates.Data.Kernel.Fi23T.Defs
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

public section

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23C CFSG.KC.Fi23T CFSG.KS.Raw.Orb

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem memS_iff {H : Nat → Nat} {s c x : Nat} : memS H s c x = true ↔ tb H (s + 1) x < c := by
  unfold memS
  exact blt_iff

theorem wJ_nil (G : Nat → Nat) (x : Nat) : wJ G [] x = x := rfl

theorem wJ_cons (G : Nat → Nat) (p : Nat) (w : List Nat) (x : Nat) :
    wJ G (p :: w) x = lJ G p (wJ G w x) := rfl

theorem lJ_pt {G : Nat → Nat} {p : Nat} (x : Nat) (hp : p < 31671) : lJ G p x = cJ G p x := by
  unfold lJ
  rw [nIf_eq, if_pos (blt_iff.2 hp)]

theorem lJ_reg {G : Nat → Nat} {p : Nat} (x : Nat) (hp : ¬ p < 31671) :
    lJ G p x = tb G (p - 31671) x := by
  unfold lJ
  rw [nIf_eq, if_neg (fun h => hp (blt_iff.1 h))]
  rfl

theorem listK_spec {H : Nat → Nat} {rl rp c bd : Nat} (h : listK H rl rp c bd = true) :
    (∀ i < c, tb H rl i < bd ∧ tb H rp (tb H rl i) = i) ∧
    (∀ i, i + 1 < c → tb H rl i < tb H rl (i + 1)) ∧
    (∀ x < bd, (tb H rp x < c ∧ tb H rl (tb H rp x) = x) ∨ tb H rp x = c) := by
  unfold listK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun x hx => ?_⟩
  · have h1 := allN_iff.1 h.1 i hi
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    exact h1
  · have h2 := allN_iff.1 h.2.1 i (by rw [Nat.pred_eq_sub_one]; omega)
    exact blt_iff.1 h2
  · have h3 := allN_iff.1 h.2.2 x hx
    rw [strictB_eq, bIf_eq] at h3
    by_cases hm : tb H rp x < c
    · rw [if_pos (blt_iff.2 hm)] at h3
      exact Or.inl ⟨hm, Nat.eq_of_beq_eq_true h3⟩
    · rw [if_neg (fun e => hm (blt_iff.1 e))] at h3
      exact Or.inr (Nat.eq_of_beq_eq_true h3)

theorem presK_spec {G H : Nat → Nat} {s c : Nat} {w : List Nat} (h : presK G H s c w = true) :
    ∀ i < c, tb H (s + 1) (wJ G w (tb H s i)) < c := fun i hi =>
  memS_iff.1 (allN_iff.1 h i hi)

theorem qK_spec {G H : Nat → Nat} {w : List Nat} (h : qK G H w = true) :
    ∀ q ∈ qL, tb H 1 (wJ G w q) < 3240 := by
  have key : ∀ L : List Nat, List.rec (motive := fun _ => Bool) true
      (fun q _ ih => Bool.rec (motive := fun _ => Bool) false ih
        (memS H (nat_lit 0) (nat_lit 3240) (wJ G w q))) L = true →
      ∀ q ∈ L, tb H 1 (wJ G w q) < 3240 := by
    intro L
    induction L with
    | nil => intro _ q hq; exact absurd hq List.not_mem_nil
    | cons a L ih =>
      intro hL q hq
      simp only [bAnd_eq, Bool.and_eq_true] at hL
      rcases List.mem_cons.1 hq with e | hq
      · rw [e]
        exact memS_iff.1 hL.1
      · exact ih hL.2 q hq
  exact key qL h

theorem foldr_count (p : Nat → Bool) (L : List Nat) :
    L.foldr (fun i a => if p i = true then a + 1 else a) 0 = (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    by_cases hp : p a = true
    · rw [if_pos hp, if_pos hp, List.length_cons]
    · rw [if_neg hp, if_neg hp]

theorem cntK_spec {G H : Nat → Nat} {w : List Nat} {c : Nat} (h : cntK G H w c = true) :
    ((List.range 3240).filter fun i => memS H 0 3240 (wJ G w (tb H 0 i))).length = c := by
  unfold cntK at h
  have e := Nat.eq_of_beq_eq_true h
  unfold cntT at e
  rw [foldN_eq] at e
  simp only [nIf_eq] at e
  rw [← e]
  exact (foldr_count _ _).symm

theorem trK_spec {G H : Nat → Nat} {b gr ng : Nat} {dom : Nat → Bool} {s lo c : Nat}
    (h : trK G H b gr ng dom s lo c = true) {j : Nat} (hlo : lo ≤ j) (hj : j < lo + c) :
    tb H b j < 31671 ∧ dom (tb H b j) = true ∧ tb H (b + 3) (tb H b j) = j ∧
      (j = s → tb H (b + 1) j = j) ∧
      (j ≠ s → s ≤ tb H (b + 1) j ∧ tb H (b + 1) j < j ∧ tb H (b + 2) j < ng ∧
        cJ G (tb H gr (tb H (b + 2) j)) (tb H b (tb H (b + 1) j)) = tb H b j) := by
  have h1 := allN_iff.1 h (j - lo) (by omega)
  have ej : Nat.add lo (j - lo) = j := Nat.add_sub_cancel' hlo
  unfold trAt at h1
  rw [ej, strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨hp, hd, hpos, hr⟩ := h1
  rw [bIf_eq] at hr
  refine ⟨blt_iff.1 hp, hd, Nat.eq_of_beq_eq_true hpos, fun e => ?_, fun e => ?_⟩
  · rw [if_pos (by rw [e]; exact Nat.beq_refl s)] at hr
    exact Nat.eq_of_beq_eq_true hr
  · rw [if_neg (fun hb => e (Nat.eq_of_beq_eq_true hb)), strictB_eq, bAnd_eq, bAnd_eq,
      bAnd_eq] at hr
    simp only [Bool.and_eq_true] at hr
    exact ⟨Nat.le_of_ble_eq_true hr.1, blt_iff.1 hr.2.1, blt_iff.1 hr.2.2.1,
      Nat.eq_of_beq_eq_true hr.2.2.2⟩

theorem covK_spec {H : Nat → Nat} {b n : Nat} {dom : Nat → Bool} (h : covK H b n dom = true)
    {x : Nat} (hx : x < 31671) (hd : dom x = true) :
    tb H (b + 3) x < n ∧ tb H b (tb H (b + 3) x) = x := by
  have h1 := allN_iff.1 h x hx
  rw [bIf_eq, if_pos hd, strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨blt_iff.1 h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem ctK_spec {G H : Nat → Nat} {b lo c : Nat} (h : ctK G H b lo c = true) {j : Nat}
    (hlo : lo ≤ j) (hj : j < lo + c) :
    tb H b j < 31671 ∧ tb H 3 (tb H b j) < 1080 ∧ tb H (b + 3) (tb H b j) = j ∧
      (j = 0 → tb H (b + 1) j = 0) ∧
      (j ≠ 0 → tb H (b + 1) j < j ∧ cJ G (tb H b (tb H (b + 1) j)) (tb H b j) = tb H b j) := by
  have h1 := allN_iff.1 h (j - lo) (by omega)
  have ej : Nat.add lo (j - lo) = j := Nat.add_sub_cancel' hlo
  unfold ctAt at h1
  rw [ej, strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨hp, hm, hpos, hr⟩ := h1
  rw [bIf_eq] at hr
  refine ⟨blt_iff.1 hp, memS_iff.1 hm, Nat.eq_of_beq_eq_true hpos, fun e => ?_, fun e => ?_⟩
  · rw [if_pos (by rw [e]; rfl)] at hr
    exact Nat.eq_of_beq_eq_true hr
  · rw [if_neg (fun hb => e (Nat.eq_of_beq_eq_true hb)), bAnd_eq] at hr
    simp only [Bool.and_eq_true] at hr
    exact ⟨blt_iff.1 hr.1, Nat.eq_of_beq_eq_true hr.2⟩

theorem boolRec_eq_true {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) (Bool.not a) a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

theorem starK_spec {G H HC : Nat → Nat} {fc c0 c1 : Nat} (h : starK G H HC fc c0 c1 = true)
    {u : Nat} (hu : u < 3510) :
    (tb H 5 u < c0 ↔ tb H 3 (tb HC 0 (tb HC 3 u)) < 1080) ∧
      (cJ G fc (tb HC 0 (tb HC 3 u)) = tb HC 0 (tb HC 3 u) ↔ tb H 7 u < c1) := by
  have h1 := allN_iff.1 h u hu
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, boolRec_eq_true, boolRec_eq_true] at h1
  simp only [memS_iff, Nat.beq_eq] at h1
  exact h1

theorem genK_spec {G H : Nat → Nat} {gr n : Nat} {fx : Bool} {f : Nat} {w : List Nat}
    (h : genK G H gr n fx f w = true) {i : Nat} (hi : i < n) :
    tb H 1 (tb H gr i) < 3240 ∧
      (fx = true → cJ G (tb H gr i) f = f) ∧ (fx = false → tb H 1 (wJ G w (tb H gr i)) < 3240) := by
  have h1 := allN_iff.1 h i hi
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h1
  refine ⟨memS_iff.1 h1.1, fun e => ?_, fun e => ?_⟩
  · have h2 := h1.2
    rw [if_pos e] at h2
    exact Nat.eq_of_beq_eq_true h2
  · have h2 := h1.2
    rw [if_neg (by rw [e]; decide)] at h2
    exact memS_iff.1 h2

end CertificateChecks.KernelFi23T

end
