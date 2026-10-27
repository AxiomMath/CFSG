
module

public import Certificates.Kernel.Sporadic.ON4.Strong
public import CFSG.Certificates.Kernel.Spor.PWord2
public import Certificates.Kernel.Sporadic.ON4.Fast

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3
open CFSG.Sporadic.ON.Native (nPts)

theorem arr_pair {g : Array Nat} {f fi : Nat → Nat} (hs : g.size = 245520)
    (hg : ∀ y < 245520, g[y]! = f y) (hp : Pair1 f fi) :
    g = Array.ofFn (n := 245520) (fun i => f i.val) ∧
      ∀ y < 245520, (pinvCand nPts g)[y]! = fi y := by
  have e := arr_ext hs hg
  refine ⟨e, fun y hy => ?_⟩
  rw [e]
  exact CFSG.KS.CB.pinvCand_get (fun x hx => (hp x hx).1) (fun x hx => (hp x hx).2.2.1) hy

theorem mW_arr {j : Nat} (hj : j < 3) : ((wordArrs Data.MWords)[j]!).size = 245520 ∧
    (∀ y < 245520, ((wordArrs Data.MWords)[j]!)[y]! = mG j y) ∧
    ∀ y < 245520, (pinvCand nPts (wordArrs Data.MWords)[j]!)[y]! = mGI j y := by
  have hs := wordArrs_size_get (ws := Data.MWords) (Nat.lt_of_lt_of_eq hj rfl)
  have hg : ∀ y < 245520, ((wordArrs Data.MWords)[j]!)[y]! = mG j y := fun y hy => (m_get hj y hy).1
  exact ⟨hs, hg, (arr_pair hs hg (pair_of mG_pair hj)).2⟩

theorem lW_arr {j : Nat} (hj : j < 2) : ((wordArrs Data.LWords)[j]!).size = 245520 ∧
    (∀ y < 245520, ((wordArrs Data.LWords)[j]!)[y]! = lG j y) ∧
    ∀ y < 245520, (pinvCand nPts (wordArrs Data.LWords)[j]!)[y]! = lGI j y := by
  have hs := wordArrs_size_get (ws := Data.LWords) (Nat.lt_of_lt_of_eq hj rfl)
  have hg : ∀ y < 245520, ((wordArrs Data.LWords)[j]!)[y]! = lG j y := fun y hy => (l_get hj y hy).1
  exact ⟨hs, hg, (arr_pair hs hg (pair_of lG_pair hj)).2⟩

theorem pcomp_size (t u : Array Nat) : (pcomp nPts t u).size = 245520 := by
  unfold pcomp
  simp

theorem mcOrig_get : (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs).size = 3 ∧
    ∀ j < 3, (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs)[j]! =
      Array.ofFn (n := 245520) fun i => mcO j i.val := by
  rw [commGens_eq]
  refine ⟨by simp; rfl, fun j hj => ?_⟩
  rw [map_get' (Nat.lt_of_lt_of_eq hj rfl)]
  obtain ⟨-, a1, a2⟩ := mW_arr (j := 1) (by norm_num)
  obtain ⟨-, b1, b2⟩ := mW_arr (j := 2) (by norm_num)
  have hX : ∀ y < 245520, (pcomp nPts (wordArrs Data.MWords)[2]! (pcomp nPts
      (wordArrs Data.MWords)[1]! (pcomp nPts (pinvCand nPts (wordArrs Data.MWords)[2]!)
        (pinvCand nPts (wordArrs Data.MWords)[1]!))))[y]! = mcX y := by
    intro y hy
    have p1 := (pair_of mG_pair (j := 1) (by norm_num)) y hy
    have p2 := (pair_of mG_pair (j := 2) (by norm_num)) _ p1.2.1
    have p3 := (pair_of mG_pair (j := 1) (by norm_num)) _ p2.2.1
    rw [pcomp_get' hy, pcomp_get' hy, pcomp_get' hy, a2 y hy, b2 _ p1.2.1, a1 _ p2.2.1,
      b1 _ p3.1]
    rfl
  interval_cases j
  · have s0 : Data.MCommutatorSpecs[0]! = (2, 3, 0) := rfl
    rw [s0]
    unfold cgen
    simp only [Nat.reduceSub, beq_self_eq_true, ↓reduceIte]
    exact arr_ext (pcomp_size _ _) fun y hy => hX y hy
  · have s1 : Data.MCommutatorSpecs[1]! = (2, 3, 2) := rfl
    rw [s1]
    unfold cgen
    simp only [Nat.reduceSub, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    refine arr_ext (pcomp_size _ _) fun y hy => ?_
    have p1 := (pair_of mG_pair (j := 1) (by norm_num)) y hy
    have pX := (mcO_pair 0 (by norm_num)) _ p1.2.1
    rw [pcomp_get' hy, pcomp_get' hy, a2 y hy, hX _ p1.2.1, a1 (mcX (mGI 1 y)) pX.1]
    rfl
  · have s2 : Data.MCommutatorSpecs[2]! = (2, 3, 3) := rfl
    rw [s2]
    unfold cgen
    simp only [Nat.reduceSub, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    refine arr_ext (pcomp_size _ _) fun y hy => ?_
    have p1 := (pair_of mG_pair (j := 2) (by norm_num)) y hy
    have pX := (mcO_pair 0 (by norm_num)) _ p1.2.1
    rw [pcomp_get' hy, pcomp_get' hy, b2 y hy, hX _ p1.2.1, b1 (mcX (mGI 2 y)) pX.1]
    rfl

theorem lcOrig_get : (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs).size = 3 ∧
    ∀ j < 3, (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs)[j]! =
      Array.ofFn (n := 245520) fun i => lcO j i.val := by
  rw [commGens_eq]
  refine ⟨by simp; rfl, fun j hj => ?_⟩
  rw [map_get' (Nat.lt_of_lt_of_eq hj rfl)]
  obtain ⟨-, a1, a2⟩ := lW_arr (j := 0) (by norm_num)
  obtain ⟨-, b1, b2⟩ := lW_arr (j := 1) (by norm_num)
  have hX : ∀ y < 245520, (pcomp nPts (wordArrs Data.LWords)[1]! (pcomp nPts
      (wordArrs Data.LWords)[0]! (pcomp nPts (pinvCand nPts (wordArrs Data.LWords)[1]!)
        (pinvCand nPts (wordArrs Data.LWords)[0]!))))[y]! = lcX y := by
    intro y hy
    have p1 := (pair_of lG_pair (j := 0) (by norm_num)) y hy
    have p2 := (pair_of lG_pair (j := 1) (by norm_num)) _ p1.2.1
    have p3 := (pair_of lG_pair (j := 0) (by norm_num)) _ p2.2.1
    rw [pcomp_get' hy, pcomp_get' hy, pcomp_get' hy, a2 y hy, b2 _ p1.2.1, a1 _ p2.2.1,
      b1 _ p3.1]
    rfl
  interval_cases j
  · have s0 : Data.LCommutatorSpecs[0]! = (1, 2, 0) := rfl
    rw [s0]
    unfold cgen
    simp only [Nat.reduceSub, beq_self_eq_true, ↓reduceIte]
    exact arr_ext (pcomp_size _ _) fun y hy => hX y hy
  · have s1 : Data.LCommutatorSpecs[1]! = (1, 2, 1) := rfl
    rw [s1]
    unfold cgen
    simp only [Nat.reduceSub, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    refine arr_ext (pcomp_size _ _) fun y hy => ?_
    have p1 := (pair_of lG_pair (j := 0) (by norm_num)) y hy
    have pX := (lcO_pair 0 (by norm_num)) _ p1.2.1
    rw [pcomp_get' hy, pcomp_get' hy, a2 y hy, hX _ p1.2.1, a1 (lcX (lGI 0 y)) pX.1]
    rfl
  · have s2 : Data.LCommutatorSpecs[2]! = (1, 2, 2) := rfl
    rw [s2]
    unfold cgen
    simp only [Nat.reduceSub, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    refine arr_ext (pcomp_size _ _) fun y hy => ?_
    have p1 := (pair_of lG_pair (j := 1) (by norm_num)) y hy
    have pX := (lcO_pair 0 (by norm_num)) _ p1.2.1
    rw [pcomp_get' hy, pcomp_get' hy, b2 y hy, hX _ p1.2.1, b1 (lcX (lGI 1 y)) pX.1]
    rfl

theorem jOrig_get : jointArrs.size = 6 ∧
    ∀ j < 6, jointArrs[j]! = Array.ofFn (n := 245520) fun i => jO j i.val := by
  have hM : (wordArrs Data.MWords).size = 3 := by
    rw [wordArrs, pwords_eq, Array.size_map]
    rfl
  unfold jointArrs
  simp only []
  rw [conjAll_eq]
  refine ⟨by simp [hM], fun j hj => ?_⟩
  rcases Nat.lt_or_ge j 3 with h | h
  · rw [getElem!_pos _ j (by simp [hM]; omega), Array.getElem_append_left (by rw [hM]; exact h),
      ← getElem!_pos _ j (by rw [hM]; exact h)]
    obtain ⟨hs, hg, -⟩ := mW_arr h
    refine arr_ext hs fun y hy => ?_
    rw [hg y hy]
    unfold jO
    rw [nIf_t (blt_of h)]
  · rw [getElem!_pos _ j (by simp [hM]; omega), Array.getElem_append_right (by rw [hM]; exact h),
      Array.getElem_map, ← getElem!_pos (wordArrs Data.MWords) (j - (wordArrs Data.MWords).size)
        (by rw [hM]; omega), hM]
    obtain ⟨-, hg, -⟩ := mW_arr (j := j - 3) (by omega)
    refine arr_ext (pcomp_size _ _) fun y hy => ?_
    obtain ⟨i1, i2⟩ := ci_get y hy
    have hc : cArr = wordArr Data.pairConjugatorWord := rfl
    rw [← hc, pcomp_get' hy, pcomp_get' hy, i1, hg _ i2, (c_get _ ((pair_of mG_pair (j := j - 3)
      (by omega)) _ i2).1).1]
    unfold jO
    have hb : Nat.blt j 3 = false := blt_false h
    rw [hb]
    rfl

theorem mc_lo {i : Nat} (hi : i < 3) : mcF i = mcO i ∧ mcFI i = mcOI i := by
  constructor <;> funext x
  · unfold mcF mcO4
    rw [nIf_t (blt_of (by omega : i < 4)), nIf_t (blt_of hi)]
  · unfold mcFI mcOI4
    rw [nIf_t (blt_of (by omega : i < 4)), nIf_t (blt_of hi)]

theorem mc_lo4 {i : Nat} (hi : i < 4) : mcF i = mcO4 i ∧ mcFI i = mcOI4 i := by
  constructor <;> funext x
  · unfold mcF
    rw [nIf_t (blt_of hi)]
  · unfold mcFI
    rw [nIf_t (blt_of hi)]

theorem mc_words : ∀ j, 3 ≤ j → j < 5 → LetM j Data.McommChain.strongWords[j]! ∧
    ∀ x < 245520, mcF j x = Data.McommChain.strongWords[j]!.foldr (GZ mcF mcFI) x := by
  intro j h3 h5
  interval_cases j
  · refine ⟨lets4.1, fun x _ => ?_⟩
    have a : mcF 3 x = mc3 x := rfl
    rw [a]
    unfold mc3
    rw [tr4_word _ _ (k := 0) (by norm_num)]
    exact foldr_congr (m := 3) (fun i hi => (mc_lo hi).1.symm) (fun i hi => (mc_lo hi).2.symm) _
      lets4.1 x
  · refine ⟨lets4.2.1, fun x _ => ?_⟩
    have a : mcF 4 x = mc4 x := rfl
    rw [a]
    unfold mc4
    rw [tr4_word _ _ (k := 1) (by norm_num)]
    exact foldr_congr (m := 4) (fun i hi => (mc_lo4 hi).1.symm) (fun i hi => (mc_lo4 hi).2.symm)
      _ lets4.2.1 x

theorem lc_lo {i : Nat} (hi : i < 3) : lcF i = lcO i ∧ lcFI i = lcOI i := by
  constructor <;> funext x
  · unfold lcF lcO5 lcO4
    rw [nIf_t (blt_of (by omega : i < 5)), nIf_t (blt_of (by omega : i < 4)), nIf_t (blt_of hi)]
  · unfold lcFI lcOI5 lcOI4
    rw [nIf_t (blt_of (by omega : i < 5)), nIf_t (blt_of (by omega : i < 4)), nIf_t (blt_of hi)]

theorem lc_lo4 {i : Nat} (hi : i < 4) : lcF i = lcO4 i ∧ lcFI i = lcOI4 i := by
  constructor <;> funext x
  · unfold lcF lcO5
    rw [nIf_t (blt_of (by omega : i < 5)), nIf_t (blt_of hi)]
  · unfold lcFI lcOI5
    rw [nIf_t (blt_of (by omega : i < 5)), nIf_t (blt_of hi)]

theorem lc_lo5 {i : Nat} (hi : i < 5) : lcF i = lcO5 i ∧ lcFI i = lcOI5 i := by
  constructor <;> funext x
  · unfold lcF
    rw [nIf_t (blt_of hi)]
  · unfold lcFI
    rw [nIf_t (blt_of hi)]

theorem lc_words : ∀ j, 3 ≤ j → j < 6 → LetM j Data.LcommChain.strongWords[j]! ∧
    ∀ x < 245520, lcF j x = Data.LcommChain.strongWords[j]!.foldr (GZ lcF lcFI) x := by
  intro j h3 h6
  interval_cases j
  · refine ⟨lets4.2.2.1, fun x _ => ?_⟩
    have a : lcF 3 x = lc3 x := rfl
    rw [a]
    unfold lc3
    rw [tr4_word _ _ (k := 2) (by norm_num)]
    exact foldr_congr (m := 3) (fun i hi => (lc_lo hi).1.symm) (fun i hi => (lc_lo hi).2.symm) _
      lets4.2.2.1 x
  · refine ⟨lets4.2.2.2.1, fun x _ => ?_⟩
    have a : lcF 4 x = lc4 x := rfl
    rw [a]
    unfold lc4
    rw [tr4_word _ _ (k := 3) (by norm_num)]
    exact foldr_congr (m := 4) (fun i hi => (lc_lo4 hi).1.symm) (fun i hi => (lc_lo4 hi).2.symm)
      _ lets4.2.2.2.1 x
  · refine ⟨lets4.2.2.2.2.1, fun x _ => ?_⟩
    have a : lcF 5 x = lc5 x := rfl
    rw [a]
    unfold lc5
    rw [tr4_word _ _ (k := 4) (by norm_num)]
    exact foldr_congr (m := 5) (fun i hi => (lc_lo5 hi).1.symm) (fun i hi => (lc_lo5 hi).2.symm)
      _ lets4.2.2.2.2.1 x

theorem j_lo {i : Nat} (hi : i < 6) : jF i = jO i ∧ jFI i = jOI i := by
  constructor <;> funext x
  · unfold jF jO8 jO7
    rw [nIf_t (blt_of (by omega : i < 8)), nIf_t (blt_of (by omega : i < 7)), nIf_t (blt_of hi)]
  · unfold jFI jOI8 jOI7
    rw [nIf_t (blt_of (by omega : i < 8)), nIf_t (blt_of (by omega : i < 7)), nIf_t (blt_of hi)]

theorem j_lo7 {i : Nat} (hi : i < 7) : jF i = jO7 i ∧ jFI i = jOI7 i := by
  constructor <;> funext x
  · unfold jF jO8
    rw [nIf_t (blt_of (by omega : i < 8)), nIf_t (blt_of hi)]
  · unfold jFI jOI8
    rw [nIf_t (blt_of (by omega : i < 8)), nIf_t (blt_of hi)]

theorem j_lo8 {i : Nat} (hi : i < 8) : jF i = jO8 i ∧ jFI i = jOI8 i := by
  constructor <;> funext x
  · unfold jF
    rw [nIf_t (blt_of hi)]
  · unfold jFI
    rw [nIf_t (blt_of hi)]

theorem j_words : ∀ j, 6 ≤ j → j < 9 → LetM j Data.jointChain.strongWords[j]! ∧
    ∀ x < 245520, jF j x = Data.jointChain.strongWords[j]!.foldr (GZ jF jFI) x := by
  intro j h6 h9
  interval_cases j
  · refine ⟨lets4.2.2.2.2.2.1, fun x _ => ?_⟩
    have a : jF 6 x = j6 x := rfl
    rw [a]
    unfold j6
    rw [tr4_word _ _ (k := 5) (by norm_num)]
    exact foldr_congr (m := 6) (fun i hi => (j_lo hi).1.symm) (fun i hi => (j_lo hi).2.symm) _
      lets4.2.2.2.2.2.1 x
  · refine ⟨lets4.2.2.2.2.2.2.1, fun x _ => ?_⟩
    have a : jF 7 x = j7 x := rfl
    rw [a]
    unfold j7
    rw [tr4_word _ _ (k := 6) (by norm_num)]
    exact foldr_congr (m := 7) (fun i hi => (j_lo7 hi).1.symm) (fun i hi => (j_lo7 hi).2.symm) _
      lets4.2.2.2.2.2.2.1 x
  · refine ⟨lets4.2.2.2.2.2.2.2, fun x _ => ?_⟩
    have a : jF 8 x = j8 x := rfl
    rw [a]
    unfold j8
    rw [tr4_word _ _ (k := 7) (by norm_num)]
    exact foldr_congr (m := 8) (fun i hi => (j_lo8 hi).1.symm) (fun i hi => (j_lo8 hi).2.symm) _
      lets4.2.2.2.2.2.2.2 x

theorem mcStrong_get : (extendStrong nPts (commGens nPts (wordArrs Data.MWords)
      Data.MCommutatorSpecs) Data.McommChain.strongWords).size = 5 ∧
    ∀ j < 5, (extendStrong nPts (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs)
      Data.McommChain.strongWords)[j]! = Array.ofFn (n := 245520) fun i => mcF j i.val := by
  refine extendStrong_get (m := 3) mcOrig_get.1 rfl (by norm_num) (fun j hj => ?_) mc_words
    (fun j hj x hx => ⟨(mcF_pair j hj x hx).1, (mcF_pair j hj x hx).2.1, (mcF_pair j hj x hx).2.2.1⟩)
  rw [mcOrig_get.2 j hj, (mc_lo hj).1]

theorem lcStrong_get : (extendStrong nPts (commGens nPts (wordArrs Data.LWords)
      Data.LCommutatorSpecs) Data.LcommChain.strongWords).size = 6 ∧
    ∀ j < 6, (extendStrong nPts (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs)
      Data.LcommChain.strongWords)[j]! = Array.ofFn (n := 245520) fun i => lcF j i.val := by
  refine extendStrong_get (m := 3) lcOrig_get.1 rfl (by norm_num) (fun j hj => ?_) lc_words
    (fun j hj x hx => ⟨(lcF_pair j hj x hx).1, (lcF_pair j hj x hx).2.1, (lcF_pair j hj x hx).2.2.1⟩)
  rw [lcOrig_get.2 j hj, (lc_lo hj).1]

theorem jStrong_get : (extendStrong nPts jointArrs Data.jointChain.strongWords).size = 9 ∧
    ∀ j < 9, (extendStrong nPts jointArrs Data.jointChain.strongWords)[j]! =
      Array.ofFn (n := 245520) fun i => jF j i.val := by
  refine extendStrong_get (m := 6) jOrig_get.1 rfl (by norm_num) (fun j hj => ?_) j_words
    (fun j hj x hx => ⟨(jF_pair j hj x hx).1, (jF_pair j hj x hx).2.1, (jF_pair j hj x hx).2.2.1⟩)
  rw [jOrig_get.2 j hj, (j_lo hj).1]

end CertificateChecks.KernelSpor.ON4K

end
