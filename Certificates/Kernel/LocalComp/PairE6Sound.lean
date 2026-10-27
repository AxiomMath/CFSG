module

public import Certificates.Kernel.LocalComp.TwistedE6TwoSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairE6Tests

public section

namespace CFSG.KC.TwistedE6Two

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
open CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two
open CFSG.ComponentClassification.RankTwoExceptional.PairE6

attribute [local irreducible] mulB powB oneB rowStarts fullRow rootB

theorem nGensP_getD_lt {k : ℕ} (hk : k < 72) : nGensP.getD k Native.one = nGen k := by
  simp [nGensP, nGens, Array.getD_eq_getD_getElem?, Array.getElem?_append, hk]

theorem nGensP_getD_ge {k : ℕ} (hk : 72 ≤ k) (hk' : k < 144) :
    nGensP.getD k Native.one = nGenW (k - 72) := by
  have h1 : ¬ k < 72 := by omega
  have h2 : k - 72 < 72 := by omega
  simp [nGensP, nGens, Array.getD_eq_getD_getElem?, Array.getElem?_append, h1, h2]

theorem size_nGensP : nGensP.size = 144 := by simp [nGensP, nGens]

theorem repAll_nGensP {V : List ℕ} (h : gensOK bracketCodes formBits rhoIdx V 0 = true)
    (hw : gensWOK bracketCodes formBits rhoIdx V 72 = true) : RepAll V nGensP 144 := by
  intro k hk
  by_cases hlt : k < 72
  · have h0 := repAll_nGens h k hlt
    rwa [nGens_getD hlt, ← nGensP_getD_lt hlt] at h0
  · have hj : k - 72 < 72 := by omega
    have hk' := allN_true hw (k - 72) hj
    rw [andB_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq,
      Nat.add_sub_cancel' (by omega : 72 ≤ k)] at hk'
    rw [nGensP_getD_ge (by omega) hk, nGenW, ← nthV_eq_getD]
    refine rep_of_eq (rep_genWK CFSG.KD.Misc.E6Std.codes formBits hj hk'.1) ?_
    rw [Nat.beq_eq]
    exact hk'.2.symm

theorem witOK_eq (X : Native.Mat) (i m : ℕ) : witOK X i m = oddN nValsP X i m := rfl

theorem pairOK_of_pairK {V : List ℕ} {n S P : ℕ} {X Y : Native.Mat} {w : List (ℕ × ℕ)}
    (h : RepAll V nValsP n) (hS : Rep S (toMat X)) (hP : Rep P (toMat Y))
    (hw : ∀ q ∈ w, q.1 < n) (hk : pairK V S w P = true) : pairOK X w Y = true := by
  unfold pairK at hk
  rw [letB_eq'] at hk
  have e : (w.all fun q => commB (nValsP.getD q.1 Native.one) Y) =
      (w.all fun q => Nat.beq (mulB (nthV V q.1) P) (mulB P (nthV V q.1))) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine ⟨fun H q hq => ?_, fun H q hq => ?_⟩
    · have := H q hq
      rwa [commB, eqM_iff_of_rep (rep_mul (h _ (hw q hq)) hP) (rep_mul hP (h _ (hw q hq)))] at this
    · rw [commB, eqM_iff_of_rep (rep_mul (h _ (hw q hq)) hP) (rep_mul hP (h _ (hw q hq)))]
      exact H q hq
  unfold pairOK
  rw [e, eqM_iff_of_rep hP rep_one, eqM_iff_of_rep hP hS]
  exact hk

theorem rep_cand {b₀ b₁ : Bool} (r : ℕ) (hr : r < 78) :
    Rep (rootB bracketCodes formBits r b₀.toNat b₁.toNat)
      (toMat (Native.rootMat bracketCodes formBits r b₀ b₁)) :=
  rep_root CFSG.KD.Misc.E6Std.codes formBits hr b₀ b₁

theorem rep_candU (a0 a1 c : Bool) :
    Rep (candUK bracketCodes formBits a0 a1 c) (toMat (candU a0 a1 c)) :=
  rep_mul (rep_mul (rep_cand 68 (by norm_num)) (rep_cand 67 (by norm_num)))
    (rep_cand (b₁ := false) 76 (by norm_num))

theorem rep_candV (a0 a1 c1 c2 c3 : Bool) :
    Rep (candVK bracketCodes formBits a0 a1 c1 c2 c3) (toMat (candV a0 a1 c1 c2 c3)) :=
  rep_mul (rep_mul (rep_mul (rep_mul (rep_cand 58 (by norm_num)) (rep_cand 54 (by norm_num)))
    (rep_cand (b₁ := false) 72 (by norm_num))) (rep_cand (b₁ := false) 74 (by norm_num)))
    (rep_cand (b₁ := false) 76 (by norm_num))

theorem pairU_of_pairUK {V : List ℕ} {n S : ℕ} (h : RepAll V nValsP n) (hS : Rep S (toMat nU))
    (hk : pairUK bracketCodes formBits V S n witsU bools = true) : pairCheckU = true := by
  unfold pairUK at hk
  rw [letB_eq'] at hk
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨hw, hp⟩ := hk
  have hlt : ∀ q ∈ witsU, q.1 < n := fun q hq => oddK_lt (hw q hq)
  unfold pairCheckU
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun q hq => ?_, fun a0 h0 a1 h1 c hc => ?_⟩
  · rw [witOK_eq]
    exact oddN_of_oddK h hS (hw q hq)
  · exact pairOK_of_pairK h hS (rep_candU a0 a1 c) hlt (hp a0 h0 a1 h1 c hc)

theorem pairV_of_pairVK {V : List ℕ} {n S : ℕ} (h : RepAll V nValsP n) (hS : Rep S (toMat nV))
    (hk : pairVK bracketCodes formBits V S n witsV bools = true) : pairCheckV = true := by
  unfold pairVK at hk
  rw [letB_eq'] at hk
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨hw, hp⟩ := hk
  have hlt : ∀ q ∈ witsV, q.1 < n := fun q hq => oddK_lt (hw q hq)
  unfold pairCheckV
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun q hq => ?_, fun a0 h0 a1 h1 c1 hc1 c2 hc2 c3 hc3 => ?_⟩
  · rw [witOK_eq]
    exact oddN_of_oddK h hS (hw q hq)
  · exact pairOK_of_pairK h hS (rep_candV a0 a1 c1 c2 c3) hlt
      (hp a0 h0 a1 h1 c1 hc1 c2 hc2 c3 hc3)

end CFSG.KC.TwistedE6Two

end
