module

public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Data.Kernel.SporSch.TitsEnum5
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.TitsEnum
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.TitsHelp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2

theorem allLt_eq_allN {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allLt n f = allN n g := by
  cases hg : allN n g
  · cases hf : allLt n f
    · rfl
    · have : allN n g = true := allN_of_forall fun i hi => by
        rw [← h i hi]
        exact allLt_spec hf hi
      rw [this] at hg
      exact absurd hg (by decide)
  · exact allLt_iff.2 fun i hi => by
      rw [h i hi]
      exact allN_spec hg i hi

theorem allL_spec {f : Nat → Bool} : ∀ {L : List Nat}, allL f L = true → ∀ x ∈ L, f x = true
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: L, h, x, hx => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allL f L) (f y) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allL_spec h2 x hx

theorem pairNe_spec : ∀ {L : List Nat}, pairNe L = true →
    L.Pairwise (fun a b => Nat.beq a b = false)
  | [], _ => List.Pairwise.nil
  | x :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (pairNe L)
        (allL (fun y => Bool.rec (motive := fun _ => Bool) true false (Nat.beq x y)) L) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    refine List.Pairwise.cons (fun y hy => ?_) (pairNe_spec h2)
    have := allL_spec h1 y hy
    cases hb : Nat.beq x y
    · rfl
    · rw [hb] at this
      exact absurd this (by decide)

theorem ext_size {S : Array (Array Nat)} {k : Nat} (hk : k ≤ S.size) : (S.extract 0 k).size = k := by
  simp [Array.size_extract]
  omega

theorem ext_get {S : Array (Array Nat)} {k i : Nat} (hk : k ≤ S.size) (hi : i < k) :
    (S.extract 0 k)[i]! = S[i]! := by
  rw [getElem!_pos _ i (by rw [ext_size hk]; exact hi), getElem!_pos S i (by omega),
    Array.getElem_extract]
  simp

abbrev C (p : Nat) : Prop := canonK 1755 11 (mask 11) (1755 * 11) p = true

@[expose] noncomputable def commK (G : Nat → Nat) (k x : Nat) : Bool :=
  allN k (fun i => eq22 1755 11 (mask 11) x (G i) (G i) x)

theorem eqA_self (a : Array Nat) : eqA 1755 a a = true := by
  unfold eqA
  exact allLt_iff.2 fun i _ => beq_self_eq_true _

theorem all5_surv (L : Array Level) (q : Array Nat → Bool) :
    all5 1755 L (fun a => !(q a) || anyEq (survivors5 1755 L q) a) = true := by
  unfold all5
  refine allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => allLt_iff.2 fun c hc =>
    allLt_iff.2 fun d hd => allLt_iff.2 fun e he => ?_
  change (!(q (prod5 1755 L a b c d e)) ||
    anyEq (survivors5 1755 L q) (prod5 1755 L a b c d e)) = true
  cases hq : q (prod5 1755 L a b c d e)
  · rfl
  · rw [Bool.not_true, Bool.false_or, anyEq, List.any_eq_true]
    refine ⟨prod5 1755 L a b c d e, ?_, eqA_self _⟩
    simp only [survivors5, List.mem_flatMap, List.mem_range, List.mem_filter, List.mem_map]
    exact ⟨a, ha, b, hb, c, hc, d, hd, ⟨e, he, rfl⟩, hq⟩

theorem isInv_of {x : Nat} (h : permOK 1755 11 (mask 11) (1755 * 11) x (pinvS 1755 11 (mask 11) x) = true) :
    isInvA 1755 (unpack 1755 11 x) (invCand 1755 (unpack 1755 11 x)) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := pinvS 1755 11 (mask 11) x) h
  rw [h1]
  exact h2

theorem hi_of {x : Nat} (h : C x) : Nat.shiftRight x (1755 * 11) = 0 := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (allN 1755 (fun i => Nat.blt (pg 11 (mask 11) x i) 1755))
        (Nat.beq (Nat.shiftRight x (1755 * 11)) (nat_lit 0))) (szOK 1755 11) = true := h
  obtain ⟨-, h2⟩ := (bAnd_iff (szOK 1755 11) _).1 h'
  exact Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (Nat.shiftRight x (1755 * 11)) (nat_lit 0))
    (allN 1755 (fun i => Nat.blt (pg 11 (mask 11) x i) 1755))).1 h2).1

end CertificateChecks.KernelSporSch.TitsHelp

end
