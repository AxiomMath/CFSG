module

public import Certificates.Kernel.ONSeven.C8135
public import Certificates.Kernel.ONSeven.BC0
public import Certificates.Kernel.ONSeven.BC1
public import Certificates.Kernel.ONSeven.BC2
public import Certificates.Kernel.ONSeven.BC3
public import Certificates.Kernel.ONSeven.BC4
public import Certificates.Kernel.ONSeven.BB0
public import Certificates.Kernel.ONSeven.BB1
public import Certificates.Kernel.ONSeven.BF3
public import Certificates.Kernel.ONSeven.BX0
public import Certificates.Kernel.ONSeven.BX1
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONS.cc0All CertificateChecks.KernelSpor.ONS.cc0S 26
#kon_join CertificateChecks.KernelSpor.ONS.cc1All CertificateChecks.KernelSpor.ONS.cc1S 26
#kon_join CertificateChecks.KernelSpor.ONS.cc2All CertificateChecks.KernelSpor.ONS.cc2S 26
#kon_join CertificateChecks.KernelSpor.ONS.cc3All CertificateChecks.KernelSpor.ONS.cc3S 26
#kon_join CertificateChecks.KernelSpor.ONS.cc4All CertificateChecks.KernelSpor.ONS.cc4S 26
#kon_join CertificateChecks.KernelSpor.ONS.fx0All CertificateChecks.KernelSpor.ONS.fx0S 8
#kon_join CertificateChecks.KernelSpor.ONS.fx1All CertificateChecks.KernelSpor.ONS.fx1S 8
#kon_join CertificateChecks.KernelSpor.ONS.fx2All CertificateChecks.KernelSpor.ONS.fx2S 8
#kon_join CertificateChecks.KernelSpor.ONS.fx3All CertificateChecks.KernelSpor.ONS.fx3S 8
#kon_join CertificateChecks.KernelSpor.ONS.fx4All CertificateChecks.KernelSpor.ONS.fx4S 8
#kon_join CertificateChecks.KernelSpor.ONS.cf3All CertificateChecks.KernelSpor.ONS.cf3S 26
#kon_join CertificateChecks.KernelSpor.ONS.cf4All CertificateChecks.KernelSpor.ONS.cf4S 26

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.CB CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU stepF invF PARf LABf Mf small' rec_get parlab parlab2
  st1 st2 allBelowN_iff')
open CertificateChecks.KernelSpor.ON3 (LetM letM_invW)
open CertificateChecks.KernelSpor.ON8 (L)

theorem invL_eq (w : List Int) : invL w = CertificateChecks.KernelSpor.ON3.invW w := rfl

theorem WW_append (a b : List Int) (x : Nat) : WW (a ++ b) x = WW a (WW b x) := by
  unfold WW
  rw [List.foldr_append]

theorem let_tw {r : Nat} (hr : r < 5) : LetM 7 (tw r) := by
  have h := lets_ok
  simp only [Bool.and_eq_true] at h
  exact letM_of (lets_all h.1.2 (getD_mem _ (by have : onSevenConjWords.size = 5 := rfl; omega)))

theorem let_xw {r : Nat} (hr : r < 5) : LetM 7 (xw r) := let_line (repIdx_lt hr)

theorem let_uw {r i : Nat} (hr : r < 5) (hi : i < (bd r).length) : LetM 7 (uw r i) := by
  have h := lets_ok
  simp only [Bool.and_eq_true] at h
  have hs : r < onSevenBadData.size := by have : onSevenBadData.size = 5 := rfl; omega
  have hm : (bd r).getD i (0, []) ∈ bd r := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  exact letM_of (lets_all (lets_all h.2 (getD_mem #[] hs)) hm)

theorem let_cw {r : Nat} (hr : r < 5) : LetM 7 (cw r) := by
  intro l hl
  unfold cw at hl
  rcases List.mem_append.1 hl with h | h
  · rcases List.mem_append.1 h with h | h
    · exact let_tw hr l h
    · exact let_xw hr l h
  · exact letM_invW (let_tw hr) l h

theorem let_bw {r i : Nat} (hr : r < 5) (hi : i < (bd r).length) : LetM 7 (bw r i) := by
  intro l hl
  unfold bw at hl
  rcases List.mem_append.1 hl with h | h
  · rcases List.mem_append.1 h with h | h
    · exact letM_invW (let_uw hr hi) l h
    · exact let_cw hr l h
  · exact let_uw hr hi l h

theorem tw_eq {r : Nat} (hr : r < 5) : onSevenConjWords[r]! = tw r :=
  (getD_eq _ _ (by have : onSevenConjWords.size = 5 := rfl; omega)).symm

theorem xp_get {r : Nat} (hr : r < 5) {i : Nat} (hi : i < 245520) :
    (onSevenConjArr r)[i]! = WW (cw r) i := by
  unfold onSevenConjArr
  rw [tw_eq hr, conj_get (let_tw hr) (fun j hj => repArr_get hr hj) (fun j hj => WW_lt hj) hi]
  unfold cw
  rw [WW_append, WW_append]
  rfl

theorem bd_get {r : Nat} (hr : r < 5) : (onSevenBadData[r]!).toList = bd r := by
  rw [← getD_eq _ _ (by have : onSevenBadData.size = 5 := rfl; omega)]
  rfl

theorem count_eq' {x : Array Nat} {Z A : Nat → Nat} (hz : ∀ p < 245520, x[p]! = Z p)
    (h0 : Z 0 = 0) (hA : ∀ k < 36, A k = trK (stepF 2) (PARf 2) (LABf 2) 36 k (Z 227759))
    (hZ : ∀ p < 245520, Z p < 245520) :
    onSevenCount x = ∑ k ∈ Finset.range 52136, ccZ Z A k := by
  obtain ⟨-, -, -, m1, m2, hf₁, hf₂⟩ := small'
  unfold onSevenCount onSevenBase
  have e := commCount_eq (levels := onSevenLevels) (stepsAll := onSevenSteps) (i₁ := 1) (i₂ := 2)
    (b₀ := 0) (b₁ := 227759) (b₂ := 100817) (z := x) (Z := Z) (A := A)
    (rec_get (by norm_num)) (rec_get (by norm_num)) (parlab (by norm_num)) parlab2 st1 st2 hf₁ hf₂
    (fun p hp => ⟨hz p hp, hZ p hp⟩) h0 (by norm_num)
    (fun k hk => by
      rw [m2] at hk ⊢
      exact hA k hk)
  rw [e, m1, m2]
  rfl

theorem slice_sums {Z A V : Nat → Nat} {s : Nat} (h : ccS Z A V s = true) :
    ∑ l ∈ Finset.range 2048, ccZ Z A (2048 * s + l) = V s := by
  have h' := Nat.eq_of_beq_eq_true h
  rw [sumR2_eq, Nat.mul_eq] at h'
  exact h'

theorem count_split {x : Array Nat} {Z A : Nat → Nat} (hz : ∀ p < 245520, x[p]! = Z p)
    (h0 : Z 0 = 0) (hA : ∀ k < 36, A k = trK (stepF 2) (PARf 2) (LABf 2) 36 k (Z 227759))
    (hZ : ∀ p < 245520, Z p < 245520) :
    onSevenCount x = ∑ s ∈ Finset.range 26, ∑ l ∈ Finset.range 2048, ccZ Z A (2048 * s + l) := by
  have ht : ∀ i, 52136 ≤ i → ccZ Z A i = 0 := fun i hi => ccF_ge hi
  rw [count_eq' hz h0 hA hZ, sum_range_tail (f := ccZ Z A) (T := 2048 * 26) ht (by norm_num),
    sum_slices]

theorem count_slices {x : Array Nat} {Z A V : Nat → Nat} (hz : ∀ p < 245520, x[p]! = Z p)
    (h0 : Z 0 = 0) (hA : ∀ k < 36, A k = trK (stepF 2) (PARf 2) (LABf 2) 36 k (Z 227759))
    (hZ : ∀ p < 245520, Z p < 245520) (hs : ∀ s < 26, ccS Z A V s = true) :
    onSevenCount x = ∑ s ∈ Finset.range 26, V s := by
  rw [count_split hz h0 hA hZ]
  exact Finset.sum_congr rfl fun s hs' => slice_sums (hs s (Finset.mem_range.1 hs'))

theorem count_ge {x : Array Nat} {Z A V : Nat → Nat} (hz : ∀ p < 245520, x[p]! = Z p)
    (h0 : Z 0 = 0) (hA : ∀ k < 36, A k = trK (stepF 2) (PARf 2) (LABf 2) 36 k (Z 227759))
    (hZ : ∀ p < 245520, Z p < 245520) {a b : Nat} (hab : a ≠ b) (ha : a < 26) (hb : b < 26)
    (h1 : ccS Z A V a = true) (h2 : ccS Z A V b = true) : V a + V b ≤ onSevenCount x := by
  rw [count_split hz h0 hA hZ, ← slice_sums h1, ← slice_sums h2,
    ← Finset.sum_pair (f := fun s => ∑ l ∈ Finset.range 2048, ccZ Z A (2048 * s + l)) hab]
  refine Finset.sum_le_sum_of_subset fun s hs => ?_
  rcases Finset.mem_insert.1 hs with h | h
  · exact Finset.mem_range.2 (h ▸ ha)
  · exact Finset.mem_range.2 ((Finset.mem_singleton.1 h) ▸ hb)

theorem sum_bij {T Ti : Nat → Nat} {f : Nat → Nat} (hT : ∀ p < 245520, T p < 245520)
    (hTi : ∀ q < 245520, Ti q < 245520) (h1 : ∀ p < 245520, Ti (T p) = p)
    (h2 : ∀ q < 245520, T (Ti q) = q) :
    ∑ q ∈ Finset.range 245520, f q = ∑ p ∈ Finset.range 245520, f (T p) := by
  refine Finset.sum_nbij' Ti T (fun q hq => ?_) (fun p hp => ?_) (fun q hq => ?_)
    (fun p hp => ?_) (fun q hq => ?_)
  · exact Finset.mem_range.2 (hTi q (Finset.mem_range.1 hq))
  · exact Finset.mem_range.2 (hT p (Finset.mem_range.1 hp))
  · exact h2 q (Finset.mem_range.1 hq)
  · exact h1 p (Finset.mem_range.1 hp)
  · rw [h2 q (Finset.mem_range.1 hq)]

theorem contains_map_fst (l : List (Nat × List Int)) (q : Nat) :
    (l.map Prod.fst).contains q = l.any fun b => Nat.beq b.1 q := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.contains_cons, List.any_cons, ih]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
    exact eq_comm

theorem badB_eq (r q : Nat) : ((bd r).map Prod.fst).contains q = badB r q :=
  contains_map_fst _ q

@[expose] noncomputable def goodI (x : Array Nat) (bad : List Nat) (q : Nat) : Nat :=
  nIf(x[q]! == q && !(bad.contains q), nat_lit 1, nat_lit 0)

theorem good_sum (x : Array Nat) (bad : List Nat) :
    (onSevenGood x bad).length = ∑ q ∈ Finset.range 245520, goodI x bad q := by
  unfold onSevenGood goodI
  rw [← cntK_eq, cntK_sum]

theorem good_term {x : Array Nat} {Z T X : Nat → Nat} {badL : List Nat} {bad : Nat → Bool}
    (hz : ∀ q < 245520, x[q]! = Z q) (hT : ∀ p < 245520, T p < 245520)
    (hZ : ∀ p < 245520, Z (T p) = T (X p))
    (hinj : ∀ p < 245520, T (X p) = T p → X p = p) (hbad : ∀ q, badL.contains q = bad q)
    {p : Nat} (hp : p < 245520) : goodI x badL (T p) = fxT X T bad p := by
  have hb : Nat.blt p 245520 = true := by rw [Nat.blt_eq]; exact hp
  unfold goodI fxT
  rw [hz _ (hT p hp), hbad, hZ p hp, hb]
  by_cases hx : X p = p
  · have h1 : Nat.beq (X p) p = true := by rw [hx]; exact Nat.beq_refl p
    rw [h1, hx, beq_self_eq_true, Bool.true_and]
    cases bad (T p) <;> rfl
  · have h1 : Nat.beq (X p) p = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hx (Nat.eq_of_beq_eq_true h)
    have h2 : (T (X p) == T p) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hx (hinj p hp (beq_iff_eq.1 h))
    rw [h1, h2, Bool.false_and]

theorem good_eq_of {x : Array Nat} {Z T Ti X : Nat → Nat} {badL : List Nat} {bad : Nat → Bool}
    (hz : ∀ q < 245520, x[q]! = Z q) (hT : ∀ p < 245520, T p < 245520)
    (hTi : ∀ q < 245520, Ti q < 245520) (h1 : ∀ p < 245520, Ti (T p) = p)
    (h2 : ∀ q < 245520, T (Ti q) = q) (hZ : ∀ p < 245520, Z (T p) = T (X p))
    (hX : ∀ p < 245520, X p < 245520) (hbad : ∀ q, badL.contains q = bad q) :
    (onSevenGood x badL).length = ∑ p ∈ Finset.range 245520, fxT X T bad p := by
  rw [good_sum, sum_bij (T := T) (Ti := Ti) hT hTi h1 h2]
  refine Finset.sum_congr rfl fun p hp => good_term hz hT hZ (fun p hp e => ?_) hbad
    (Finset.mem_range.1 hp)
  rw [← h1 _ (hX p hp), e, h1 p hp]

theorem good_eq {r : Nat} (hr : r < 5) :
    (onSevenGood (onSevenConjArr r) ((onSevenBadData[r]!).toList.map Prod.fst)).length =
      ∑ p ∈ Finset.range 245520, fxT (WW (xw r)) (WW (tw r)) (badB r) p := by
  have hT := let_tw hr
  rw [bd_get hr]
  refine good_eq_of (Z := WW (cw r)) (Ti := WW (invL (tw r))) (fun q hq => xp_get hr hq)
    (fun p hp => WW_lt hp) (fun q hq => WW_lt hq) (fun p hp => WW_inv hT hp)
    (fun q hq => WW_inv' hT hq) (fun p hp => ?_) (fun p hp => WW_lt hp) (badB_eq r)
  unfold cw
  rw [WW_append, WW_append, invL_eq, WW_inv hT hp]

theorem good_slices {r : Nat} (hr : r < 5) {V : Nat → Nat}
    (hs : ∀ s < 8, fxS (WW (xw r)) (WW (tw r)) (badB r) V s = true) :
    (onSevenGood (onSevenConjArr r) ((onSevenBadData[r]!).toList.map Prod.fst)).length =
      ∑ s ∈ Finset.range 8, V s := by
  have ht : ∀ i, 245520 ≤ i → fxT (WW (xw r)) (WW (tw r)) (badB r) i = 0 := by
    intro i hi
    have hb : Nat.blt i 245520 = false := by
      rw [Bool.eq_false_iff]
      intro e
      rw [Nat.blt_eq] at e
      omega
    unfold fxT
    rw [hb]
  rw [good_eq hr, sum_range_tail (T := 30720 * 8) ht (by norm_num), sum_slices]
  refine Finset.sum_congr rfl fun s hs' => ?_
  have h' := Nat.eq_of_beq_eq_true (hs s (Finset.mem_range.1 hs'))
  unfold fxS at h'
  rw [sumR2_eq, Nat.mul_eq] at h'
  exact h'

@[expose] noncomputable def smallB : Bool :=
  (List.range 5).all fun r => Nat.beq (WW (cw r) 0) 0 &&
    (allN 36 fun k => Nat.beq ((AL r).getD k 0)
      (trK (stepF 2) (PARf 2) (LABf 2) 36 k (WW (cw r) 227759))) &&
    (List.range (bd r).length).all fun i => Nat.beq (WW (uw r i) 0) ((bd r).getD i (0, [])).1 &&
      (Nat.blt r 3 && Nat.beq (WW (bw r i) 0) 0 &&
        (allN 36 fun k => Nat.beq ((ABL r i).getD k 0)
          (trK (stepF 2) (PARf 2) (LABf 2) 36 k (WW (bw r i) 227759))) || !(Nat.blt r 3))

theorem small_ok : smallB = true := by quickRfl

end CertificateChecks.KernelSpor.ONS

end
