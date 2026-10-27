module

public import Certificates.Data.Kernel.Fi23S.Defs
public import CFSG.Sporadic.Fi23.InvCertInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23S CFSG.KS.Raw.Orb CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

theorem cyK_zero (h : Nat → Nat) (q l x : Nat) :
    cyK h q 0 l x = if x = q then l else 0 := by
  change Bool.rec (motive := fun _ => Nat) 0 l (Nat.beq x q) = _
  rw [nIf_eq]
  simp only [Nat.beq_eq]

theorem cyK_succ (h : Nat → Nat) (q f l x : Nat) :
    cyK h q (f + 1) l x = if x = q then l else cyK h q f (l + 1) (h x) := by
  change Bool.rec (motive := fun _ => Nat) (cyK h q f (Nat.succ l) (h x)) l (Nat.beq x q) = _
  rw [nIf_eq]
  simp only [Nat.beq_eq, Nat.succ_eq_add_one]

abbrev cBody (h : Nat → Nat) (q : Nat) (l : Nat) (s : Option Nat × Nat) :
    Id (ForInStep (Option Nat × Nat)) :=
  if (s.2 == q) = true then pure (ForInStep.done (some l, s.2))
  else pure (ForInStep.yield (none, h s.2))

theorem loop (h : Nat → Nat) (q : Nat) : ∀ n l x, 0 < l →
    (forIn (m := Id) (List.range' l (n + 1)) ((none : Option Nat), x) (cBody h q)).1 =
      if cyK h q n l x = 0 then none else some (cyK h q n l x)
  | 0, l, x, hl => by
    rw [List.range'_succ, List.range'_zero, List.forIn_cons, cyK_zero]
    by_cases hx : x = q
    · subst hx
      have hl0 : l ≠ 0 := by omega
      simp [cBody, hl0]
      rfl
    · simp [cBody, hx]
      rfl
  | n + 1, l, x, hl => by
    rw [List.range'_succ, List.forIn_cons, cyK_succ]
    by_cases hx : x = q
    · subst hx
      have hl0 : l ≠ 0 := by omega
      simp [cBody, hl0]
      rfl
    · have ih := loop h q n (l + 1) (h x) (by omega)
      simp only [cBody, hx, if_false, beq_iff_eq, pure_bind]
      exact ih

theorem cycLen_eq (P R : Table) (q : Nat) :
    cycLen P R q = cyK (fun y => ap P (ap R y)) q 119 1 (ap P (ap R q)) := by
  have hl := loop (fun y => ap P (ap R y)) q 119 1 (ap P (ap R q)) (by norm_num)
  simp only [cBody, Nat.reduceAdd] at hl
  unfold cycLen
  simp only [Id.run_bind, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv]
  split
  · rename_i r heq
    try simp only [Id.run] at heq
    rw [hl] at heq
    split_ifs at heq with h0 <;>
      first | exact (Option.some.inj heq).symm | exact absurd heq (by simp)
  · rename_i heq
    try simp only [Id.run] at heq
    rw [hl] at heq
    split_ifs at heq with h0 <;> first | exact h0.symm | exact absurd heq (by simp)

theorem cyK_spec (h : Nat → Nat) (q : Nat) : ∀ f l x c, cyK h q f l x = c → c ≠ 0 →
    l ≤ c ∧ Nat.repeat h (c - l) x = q
  | 0, l, x, c, e, hc => by
    rw [cyK_zero] at e
    split_ifs at e with hx
    · subst e
      exact ⟨le_rfl, by rw [Nat.sub_self]; exact hx⟩
    · exact absurd e.symm hc
  | f + 1, l, x, c, e, hc => by
    rw [cyK_succ] at e
    split_ifs at e with hx
    · subst e
      exact ⟨le_rfl, by rw [Nat.sub_self]; exact hx⟩
    · obtain ⟨h1, h2⟩ := cyK_spec h q f (l + 1) (h x) c e hc
      refine ⟨by omega, ?_⟩
      have e2 : c - l = (c - (l + 1)) + 1 := by omega
      rw [e2, ← h2]
      clear h2 e2
      generalize c - (l + 1) = m
      induction m with
      | zero => rfl
      | succ m ih => rw [Nat.repeat, ih]; rfl

theorem repeat_add (h : Nat → Nat) (a b x : Nat) :
    Nat.repeat h (a + b) x = Nat.repeat h a (Nat.repeat h b x) := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [Nat.succ_add, Nat.repeat, ih]; rfl

theorem repeat_mul (h : Nat → Nat) {c x : Nat} (hc : Nat.repeat h c x = x) :
    ∀ k, Nat.repeat h (c * k) x = x
  | 0 => rfl
  | k + 1 => by rw [Nat.mul_succ, Nat.add_comm, repeat_add, repeat_mul h hc k, hc]

theorem repeat_dvd (h : Nat → Nat) {c m x : Nat} (hc : Nat.repeat h c x = x) (hd : c ∣ m) :
    Nat.repeat h m x = x := by
  obtain ⟨k, rfl⟩ := hd
  exact repeat_mul h hc k

theorem odd_lcm {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) : Nat.lcm a b % 2 = 1 := by
  have hd : Nat.lcm a b ∣ a * b := Nat.lcm_dvd (Nat.dvd_mul_right a b) (Nat.dvd_mul_left b a)
  have hab : (a * b) % 2 = 1 := by rw [Nat.mul_mod, ha, hb]
  rcases Nat.mod_two_eq_zero_or_one (Nat.lcm a b) with h | h
  · exact absurd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) hd) (by omega)
  · exact h

abbrev oBody (c : Nat → Nat) (q : Nat) (s : Option Nat × Nat) :
    Id (ForInStep (Option Nat × Nat)) :=
  if (c q % 2 == 0) = true then pure (ForInStep.done (some 0, s.2))
  else pure (ForInStep.yield (none, s.2.lcm (c q)))

theorem loop2 (c : Nat → Nat) : ∀ (qs : List Nat) (L : Nat), (∀ q ∈ qs, c q % 2 = 1) →
    forIn (m := Id) qs ((none : Option Nat), L) (oBody c) =
      ((none : Option Nat), qs.foldl (fun L q => L.lcm (c q)) L)
  | [], L, _ => rfl
  | q :: qs, L, h => by
    have hq : c q % 2 = 1 := h q List.mem_cons_self
    have hne : ¬ ((c q % 2 == 0) = true) := by rw [hq]; decide
    rw [List.forIn_cons]
    simp only [oBody, hne, if_false, pure_bind, List.foldl_cons]
    exact loop2 c qs _ fun q' hq' => h q' (List.mem_cons_of_mem q hq')

theorem foldl_odd (c : Nat → Nat) : ∀ (qs : List Nat) (L : Nat), L % 2 = 1 →
    (∀ q ∈ qs, c q % 2 = 1) → (qs.foldl (fun L q => L.lcm (c q)) L) % 2 = 1
  | [], _, hL, _ => hL
  | q :: qs, L, hL, h => foldl_odd c qs _ (odd_lcm hL (h q List.mem_cons_self))
      fun q' hq' => h q' (List.mem_cons_of_mem q hq')

theorem foldl_dvd (c : Nat → Nat) : ∀ (qs : List Nat) (L : Nat),
    L ∣ qs.foldl (fun L q => L.lcm (c q)) L ∧ ∀ q ∈ qs, c q ∣ qs.foldl (fun L q => L.lcm (c q)) L
  | [], _ => ⟨dvd_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | q :: qs, L => by
    obtain ⟨h1, h2⟩ := foldl_dvd c qs (L.lcm (c q))
    refine ⟨Nat.dvd_trans (Nat.dvd_lcm_left _ _) h1, fun q' hq' => ?_⟩
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact Nat.dvd_trans (Nat.dvd_lcm_right _ _) h1
    · exact h2 q' hq'

theorem oddOK_of (P R : Table)
    (hc : ∀ q < 6, cyK (fun y => ap P (ap R y)) q 119 1 (ap P (ap R q)) % 2 = 1) :
    oddOK P R = true := by
  have hq : ∀ q < 6, cycLen P R q % 2 = 1 := fun q hq => by rw [cycLen_eq]; exact hc q hq
  have hfix : ∀ q < 6, Nat.repeat (fun y => ap P (ap R y)) (cycLen P R q) q = q := by
    intro q hq'
    have h1 := hc q hq'
    rw [cycLen_eq]
    obtain ⟨hle, hr⟩ := cyK_spec (fun y => ap P (ap R y)) q 119 1 (ap P (ap R q)) _ rfl
      (by omega)
    generalize cyK (fun y => ap P (ap R y)) q 119 1 (ap P (ap R q)) = c at hle hr h1 ⊢
    have e : c = (c - 1) + 1 := by omega
    rw [e, repeat_add]
    exact hr
  have hQ : chainQ.toList = [0, 1, 2, 3, 4, 5] := rfl
  have hall : ∀ q ∈ chainQ.toList, cycLen P R q % 2 = 1 := by
    rw [hQ]
    intro q hq'
    exact hq q (by simp at hq'; omega)
  have hord : oddOrd P R = chainQ.toList.foldl (fun L q => L.lcm (cycLen P R q)) 1 := by
    have e := loop2 (cycLen P R) chainQ.toList 1 hall
    try simp only [oBody] at e
    unfold oddOrd
    simp only [Id.run_bind]
    rw [← Array.forIn_toList, e]
    rfl
  unfold oddOK
  rw [hord, Bool.and_eq_true, beq_iff_eq]
  refine ⟨foldl_odd _ _ 1 rfl hall, ?_⟩
  unfold fixQ
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 6 := hi
  rw [beq_iff_eq]
  unfold iterPR
  have hmem : chainQ[i] ∈ chainQ.toList := Array.getElem_mem_toList hi
  have hlt : chainQ[i] < 6 := by
    rw [hQ] at hmem
    simp at hmem
    omega
  exact repeat_dvd _ (hfix _ hlt) ((foldl_dvd (cycLen P R) chainQ.toList 1).2 _ hmem)

end CertificateChecks.KernelFi23S

end
