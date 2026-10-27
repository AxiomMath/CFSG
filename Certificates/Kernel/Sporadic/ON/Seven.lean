module

public import Certificates.Kernel.Sporadic.ON.Minus2124
public import Certificates.Kernel.Sporadic.ON.SevenCC
public import Certificates.Kernel.Sporadic.ON.SevenFx
public import CFSG.RankThree.Native.ONSevenArrays
public import CFSG.Sporadic.Schreier.ONVectorData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ONCheckChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
  CFSG.RankThree.Native

theorem TT_UU {h y : Nat} (hh : h < 7) (hy : y < 245520) : TT h (UU h y) = y := by
  obtain ⟨x, hx, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 245520)
    (t := Finset.range 245520) (fun x _ => TT h x)
    (fun x hx => Finset.mem_range.2 (perm_facts' x (Finset.mem_range.1 hx) h hh).1)
    (fun a b ha hb hab => calc
      a = UU h (TT h a) := (perm_facts' a (Finset.mem_range.1 ha) h hh).2.2.symm
      _ = UU h (TT h b) := congrArg (UU h) hab
      _ = b := (perm_facts' b (Finset.mem_range.1 hb) h hh).2.2)
    le_rfl y (Finset.mem_range.2 hy)
  rw [e, (perm_facts' x (Finset.mem_range.1 hx) h hh).2.2]

theorem small : bAnd(Nat.beq (TT 5 0) 0, bAnd(Nat.beq (TT 5 100817) 181206,
    bAnd(Nat.beq (TT 5 227759) 227759, bAnd(Nat.beq (Mf 1) 52136, bAnd(Nat.beq (Mf 2) 36,
    bAnd(allN 10 fun j => Nat.beq (stepF 1 j 0) 0,
      allN 4 fun j => bAnd(Nat.beq (stepF 2 j 0) 0, Nat.beq (stepF 2 j 227759) 227759))))))) =
    true := by quickRfl

theorem small' : TT 5 0 = 0 ∧ TT 5 100817 = 181206 ∧ TT 5 227759 = 227759 ∧ Mf 1 = 52136 ∧
    Mf 2 = 36 ∧ (∀ j < 10, stepF 1 j 0 = 0) ∧
    ∀ j < 4, stepF 2 j 0 = 0 ∧ stepF 2 j 227759 = 227759 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := (by simpa only [bAnd_iff] using small :
    Nat.beq (TT 5 0) 0 = true ∧ Nat.beq (TT 5 100817) 181206 = true ∧
    Nat.beq (TT 5 227759) 227759 = true ∧ Nat.beq (Mf 1) 52136 = true ∧
    Nat.beq (Mf 2) 36 = true ∧ (allN 10 fun j => Nat.beq (stepF 1 j 0) 0) = true ∧
    (allN 4 fun j => bAnd(Nat.beq (stepF 2 j 0) 0, Nat.beq (stepF 2 j 227759) 227759)) = true)
  refine ⟨Nat.eq_of_beq_eq_true n1, Nat.eq_of_beq_eq_true n2, Nat.eq_of_beq_eq_true n3,
    Nat.eq_of_beq_eq_true n4, Nat.eq_of_beq_eq_true n5,
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec n6 j hj), fun j hj => ?_⟩
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec n7 j hj)
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem x_get {i : Nat} (hi : i < 245520) : (onSevenArr [6])[i]! = TT 5 i := by
  have hp : pletter qonStrongArrs onSevenInvArrs 6 = qonStrongArrs[5]! := by
    simp [pletter]
  unfold onSevenArr
  simp only [pword]
  rw [hp]
  unfold Native.pcomp pid
  rw [ofFn_get hi, ofFn_get hi, qon_SA]
  exact SA_get (by norm_num) hi

theorem parlab2 : ∀ k < Mf 2, PARf 2 k < Mf 2 ∧ LABf 2 k < Nat.mul 2 (len 2) := by
  intro k hk
  have hp : cbPt 245520 (Mf 2) (Nat.mul 2 (len 2)) (stepF 2) (PTSf 2) (POSf 2) (PARf 2)
      (LABf 2) k = true := ptL_of pt2All (by decide) k hk
  unfold cbPt at hp
  rw [strictB_eq', strictB_eq', strictB_eq'] at hp
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h, -⟩ := (bAnd_iff _ _).1 h
  by_cases h0 : k = 0
  · subst h0
    decide
  · have hb : Nat.beq k (nat_lit 0) = false := by
      cases k with
      | zero => exact absurd rfl h0
      | succ k => rfl
    rw [hb] at h
    obtain ⟨a, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨b, -⟩ := (bAnd_iff _ _).1 h
    exact ⟨by have := Nat.blt_eq ▸ a; omega, Nat.blt_eq ▸ b⟩

theorem stepF_lo {i j x : Nat} (h : Nat.blt j (len i) = true) :
    stepF i j x = TT (Nat.add (off i) j) x := by
  unfold stepF
  rw [h]

theorem stepF_hi {i j x : Nat} (h : Nat.blt j (len i) = false) :
    stepF i j x = UU (Nat.add (off i) (Nat.sub j (len i))) x := by
  unfold stepF
  rw [h]

theorem invF_lo {i j x : Nat} (h : Nat.blt j (len i) = true) :
    invF i j x = UU (Nat.add (off i) j) x := by
  unfold invF
  rw [h]

theorem invF_hi {i j x : Nat} (h : Nat.blt j (len i) = false) :
    invF i j x = TT (Nat.add (off i) (Nat.sub j (len i))) x := by
  unfold invF
  rw [h]

theorem st1 : ∀ j < 10, ∀ x < 245520, ((onSevenSteps[1]!)[j]!)[x]! = stepF 1 j x ∧
    stepF 1 j x < 245520 ∧ invF 1 j x < 245520 ∧ invF 1 j (stepF 1 j x) = x ∧
    stepF 1 j (invF 1 j x) = x := by
  intro j hj x hx
  refine ⟨steps_get' (by norm_num) hj hx, ?_⟩
  rcases Nat.lt_or_ge j 5 with h5 | h5
  · have hb : Nat.blt j (len 1) = true := Nat.blt_eq ▸ h5
    have hh : Nat.add (off 1) j < 7 := by
      change 2 + j < 7
      omega
    simp only [stepF_lo hb, invF_lo hb]
    have hf := perm_facts' x hx _ hh
    exact ⟨hf.1, hf.2.1, hf.2.2, TT_UU hh hx⟩
  · have hb : Nat.blt j (len 1) = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact absurd (Nat.blt_eq ▸ e : j < 5) (by omega)
    have hh : Nat.add (off 1) (Nat.sub j (len 1)) < 7 := by
      change 2 + (j - 5) < 7
      omega
    simp only [stepF_hi hb, invF_hi hb]
    have hf := perm_facts' x hx _ hh
    exact ⟨hf.2.1, hf.1, TT_UU hh hx, hf.2.2⟩

theorem st2 : ∀ j < 4, ∀ x < 245520, ((onSevenSteps[2]!)[j]!)[x]! = stepF 2 j x ∧
    stepF 2 j x < 245520 := by
  intro j hj x hx
  refine ⟨steps_get' (by norm_num) hj hx, ?_⟩
  unfold stepF
  cases Nat.blt j (len 2)
  · exact UU_lt hx
  · exact TT_lt hx

theorem rec_get {i : Nat} (hi : i < 29) : onSevenLevels[i]! =
    ⟨Array.ofFn (n := Mf i) fun k => PTSf i k.val, Array.ofFn (n := 245520) fun z => POSf i z.val,
      Array.ofFn (n := Mf i) fun k => PARf i k.val, Array.ofFn (n := Mf i) fun k => LABf i k.val⟩ := by
  have hL : onSevenLevels = _ := cLevels_eq'
  rw [hL, ofFn_get hi]

theorem count_eq : onSevenCount (onSevenArr [6]) = ∑ k ∈ Finset.range (Mf 1), ccX k := by
  obtain ⟨h0, -, h7, -, -, hf₁, hf₂⟩ := small'
  unfold onSevenCount onSevenBase
  have e := commCount_eq (levels := onSevenLevels) (stepsAll := onSevenSteps) (i₁ := 1) (i₂ := 2)
    (b₀ := 0) (b₁ := 227759) (b₂ := 100817) (z := onSevenArr [6]) (Z := TT 5)
    (A := fun _ => 227759) (rec_get (by norm_num))
    (rec_get (by norm_num)) (parlab (by norm_num)) parlab2 st1 st2 hf₁ hf₂
    (fun p hp => ⟨x_get hp, TT_lt hp⟩) h0 (by norm_num)
    (fun k hk => by
      rw [h7, trK_fix parlab2 (fun j hj => (hf₂ j hj).2) _ _ hk])
  rw [e]
  have m1 : Mf 1 = 52136 := small'.2.2.2.1
  have m2 : Mf 2 = 36 := small'.2.2.2.2.1
  unfold ccX
  rw [m1, m2]

theorem ccAll : ∀ s < 26, ccOK s = true := by
  intro s hs
  interval_cases s
  · exact cc0
  · exact cc1
  · exact cc2
  · exact cc3
  · exact cc4
  · exact cc5
  · exact cc6
  · exact cc7
  · exact cc8
  · exact cc9
  · exact cc10
  · exact cc11
  · exact cc12
  · exact cc13
  · exact cc14
  · exact cc15
  · exact cc16
  · exact cc17
  · exact cc18
  · exact cc19
  · exact cc20
  · exact cc21
  · exact cc22
  · exact cc23
  · exact cc24
  · exact cc25

theorem fxAll : ∀ s < 8, fxOK s = true := by
  intro s hs
  interval_cases s
  · exact fx0
  · exact fx1
  · exact fx2
  · exact fx3
  · exact fx4
  · exact fx5
  · exact fx6
  · exact fx7

theorem cuAll : ∀ s < 8, cuOK s = true := by
  intro s hs
  interval_cases s
  · exact cu0
  · exact cu1
  · exact cu2
  · exact cu3
  · exact cu4
  · exact cu5
  · exact cu6
  · exact cu7

theorem count_36 : onSevenCount (onSevenArr [6]) = 36 := by
  have m1 : Mf 1 = 52136 := small'.2.2.2.1
  have hs : ∀ s ∈ Finset.range 26, ∑ l ∈ Finset.range 2048, ccX (2048 * s + l) = ccV s := by
    intro s hs
    have h' := Nat.eq_of_beq_eq_true (ccAll s (Finset.mem_range.1 hs))
    rw [sumR2_eq, Nat.mul_eq] at h'
    exact h'
  have ht : ∀ i, 52136 ≤ i → ccX i = 0 := fun i hi => ccF_ge hi
  rw [count_eq, m1, sum_range_tail (f := ccX) (T := 2048 * 26) ht (by norm_num), sum_slices,
    Finset.sum_congr rfl hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem good_90 : (onSevenGood (onSevenArr [6]) []).length = 90 := by
  have hs : ∀ s ∈ Finset.range 8, ∑ l ∈ Finset.range 30720, fxF (30720 * s + l) = fxV s := by
    intro s hs
    have h' := Nat.eq_of_beq_eq_true (fxAll s (Finset.mem_range.1 hs))
    rw [sumR2_eq, Nat.mul_eq] at h'
    exact h'
  have hq : ((List.range 245520).filter fun q =>
      (onSevenArr [6])[q]! == q && !(([] : List Nat).contains q)) =
      (List.range 245520).filter fun q => Nat.beq (TT 5 q) q := by
    refine List.filter_congr fun q hq => ?_
    have hq : q < 245520 := List.mem_range.1 hq
    rw [Bool.eq_iff_iff]
    simp [x_get hq]
  have e : ∑ i ∈ Finset.range 245520, nIf(Nat.beq (TT 5 i) i, nat_lit 1, nat_lit 0) =
      ∑ i ∈ Finset.range 245520, fxF i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hb : Nat.blt i 245520 = true := Nat.blt_eq ▸ Finset.mem_range.1 hi
    unfold fxF
    rw [hb]
  have ht : ∀ i, 245520 ≤ i → fxF i = 0 := by
    intro i hi
    have hb : Nat.blt i 245520 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact absurd (Nat.blt_eq ▸ e) (by omega)
    unfold fxF
    rw [hb]
  have hn : nPts () = 245520 := rfl
  unfold onSevenGood
  rw [hn, hq, ← cntK_eq, cntK_sum, e, sum_range_tail (T := 30720 * 8) ht (by norm_num), sum_slices,
    Finset.sum_congr rfl hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem cube : ∀ q < 245520, TT 5 (TT 5 (TT 5 q)) = q := by
  intro q hq
  have h := cuAll (q / 30690) (by omega)
  have h' := allN_spec h (q % 30690) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (q / 30690) 30690) (q % 30690) = q := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  beta_reduce at h'
  rw [e] at h'
  exact Nat.eq_of_beq_eq_true h'

theorem pcomp_get {n : Nat} {t u : Array Nat} {i : Nat} (hi : i < n) :
    (Native.pcomp n t u)[i]! = t[u[i]!]! := by
  unfold Native.pcomp
  exact ofFn_get hi

theorem pid_get {n i : Nat} (hi : i < n) : (pid n)[i]! = i := by
  unfold pid
  exact ofFn_get hi

theorem allBelowN_iff' {n : Nat} {p : Nat → Bool} :
    allBelowN n p = true ↔ ∀ i < n, p i = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem peq_of {n : Nat} {t u : Array Nat} (h : ∀ i < n, t[i]! = u[i]!) : peq n t u = true := by
  unfold peq
  refine allBelowN_iff'.2 fun i hi => ?_
  rw [h i hi, beq_self_eq_true]

theorem peq_false_of {n i : Nat} {t u : Array Nat} (hi : i < n) (h : t[i]! ≠ u[i]!) :
    peq n t u = false := by
  rw [Bool.eq_false_iff]
  intro hp
  unfold peq at hp
  exact h (beq_iff_eq.1 (allBelowN_iff'.1 hp i hi))

theorem seven_facts : (onSevenArr [6])[0]! = 0 ∧ (onSevenGood (onSevenArr [6]) []).length = 90 ∧
    onSevenCount (onSevenArr [6]) = 36 ∧
    peq N (Native.pcomp N (onSevenArr [6]) (Native.pcomp N (onSevenArr [6]) (onSevenArr [6]))) (pid N) = true ∧
    peq N (onSevenArr [6]) (pid N) = false := by
  obtain ⟨h0, h2, -⟩ := small'
  refine ⟨by rw [x_get (i := 0) (by norm_num), h0], good_90, count_36, peq_of fun i hi => ?_,
    peq_false_of (i := 100817) (by norm_num) ?_⟩
  · have hi' : i < 245520 := hi
    rw [pcomp_get hi, pcomp_get hi, x_get hi', x_get (TT_lt hi'), x_get (TT_lt (TT_lt hi')),
      cube i hi', pid_get hi]
  · rw [x_get (i := 100817) (by norm_num), pid_get (n := N) (by norm_num), h2]
    decide

end CertificateChecks.KernelSpor.ON

end
