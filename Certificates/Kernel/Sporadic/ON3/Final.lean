module

public import Certificates.Kernel.Sporadic.ON3.Sift
public import Certificates.Kernel.Sporadic.ON3.U
public import Certificates.Kernel.Sporadic.ON3.CC
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON3.fxAll CertificateChecks.KernelSpor.ON3.fxOK 8
#kon_join CertificateChecks.KernelSpor.ON3.ccAll CertificateChecks.KernelSpor.ON3.ccOK 26

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.PW CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.Sporadic.ON.Native (nPts)
open CertificateChecks.KernelSpor.ON (TT UU stepF invF PARf LABf Mf small' rec_get parlab parlab2
  st1 st2)

theorem peq_of' {t u : Array Nat} (h : ∀ i < 245520, t[i]! = u[i]!) : peq nPts t u = true := by
  unfold peq
  refine allBelowN_iff.2 fun i hi => ?_
  rw [h i hi, beq_self_eq_true]

theorem peq_false_of' {i : Nat} {t u : Array Nat} (hi : i < 245520) (h : t[i]! ≠ u[i]!) :
    peq nPts t u = false := by
  rw [Bool.eq_false_iff]
  intro hp
  unfold peq at hp
  exact h (beq_iff_eq.1 (allBelowN_iff.1 hp i hi))

theorem bB_lt {k : Nat} (hk : k < 3) : bB k < 245520 := (base_facts.2 k hk).2

theorem fix_240 : fixCount nPts zArr = 240 := by
  have hs : ∀ s ∈ Finset.range 8, ∑ l ∈ Finset.range 30720, fxF (30720 * s + l) = fxV s := by
    intro s hs
    have h' := Nat.eq_of_beq_eq_true (fxAll s (Finset.mem_range.1 hs))
    rw [sumR2_eq, Nat.mul_eq] at h'
    exact h'
  have hq : ((List.range 245520).filter fun i => zArr[i]! == i) =
      (List.range 245520).filter fun q => Nat.beq (ZT q) q := by
    refine List.filter_congr fun q hq => ?_
    have hq : q < 245520 := List.mem_range.1 hq
    rw [(z_get q hq).1]
    rfl
  have e : ∑ i ∈ Finset.range 245520, nIf(Nat.beq (ZT i) i, nat_lit 1, nat_lit 0) =
      ∑ i ∈ Finset.range 245520, fxF i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hb : Nat.blt i 245520 = true := blt_of (Finset.mem_range.1 hi)
    unfold fxF
    rw [hb]
  have ht : ∀ i, 245520 ≤ i → fxF i = 0 := by
    intro i hi
    have hb : Nat.blt i 245520 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact absurd (by simpa using e : i < 245520) (by omega)
    unfold fxF
    rw [hb]
  unfold fixCount
  rw [hq, ← cntK_eq, cntK_sum, e, sum_range_tail (T := 30720 * 8) ht (by norm_num), sum_slices,
    Finset.sum_congr rfl hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem z_part : peq nPts (pcomp nPts zArr zArr) (pid nPts) = true ∧ peq nPts zArr (pid nPts) = false ∧
    memIn TStrong Data.TChain.base zArr = true ∧ fixCount nPts zArr = 240 ∧ zArr[0]! = 0 ∧
    allBelowN 3 (fun j => peq nPts (pcomp nPts (wordArrs Data.MWords)[j]! zArr)
      (pcomp nPts zArr (wordArrs Data.MWords)[j]!)) = true := by
  refine ⟨peq_of' fun i hi => ?_, peq_false_of' (i := 1) (by norm_num) ?_,
    memT (fun k hk => (z_get _ (bB_lt hk)).1) (fun k hk => (z_get _ (bB_lt hk)).2) sifts.1, fix_240, ?_, allBelowN_iff.2 fun j hj => ?_⟩
  · obtain ⟨z1, z2⟩ := z_get i hi
    rw [pcomp_get' hi, z1, (z_get _ z2).1, (tab_facts hi).2.2.2.2.2.2.2.2.2.2.2.2.2.1, pid_get' hi]
  · rw [(z_get 1 (by norm_num)).1, pid_get' (by norm_num)]
    decide +kernel
  · rw [(z_get 0 (by norm_num)).1]
    decide +kernel
  · refine peq_of' fun i hi => ?_
    obtain ⟨z1, z2⟩ := z_get i hi
    obtain ⟨g1, g2⟩ := m_get hj i hi
    rw [pcomp_get' hi, pcomp_get' hi, z1, g1, (m_get hj _ z2).1, (z_get _ g2).1]
    have hf := tab_facts hi
    interval_cases j
    · rfl
    · exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem comm_part : commCount (cLevels nPts Data.baseList.toArray
      (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray))
    (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray) 1 2 zArr
    #[0, 227759, 100817] = 672 := by
  obtain ⟨-, -, -, m1, m2, hf₁, hf₂⟩ := small'
  have e := commCount_eq (n := 245520) (i₁ := 1) (i₂ := 2) (b₀ := 0) (b₁ := 227759) (b₂ := 100817)
    (z := zArr) (Z := ZT) (A := ccA) (rec_get (by norm_num)) (rec_get (by norm_num))
    (parlab (by norm_num)) parlab2 st1 st2 hf₁ hf₂ (fun p hp => z_get p hp)
    (by decide +kernel) (by norm_num)
    (fun k _ => by unfold ccA; rw [m2])
  rw [e, m1]
  have hs : ∀ s ∈ Finset.range 26, ∑ l ∈ Finset.range 2048, ccX (2048 * s + l) = ccV s := by
    intro s hs
    have h' := Nat.eq_of_beq_eq_true (ccAll s (Finset.mem_range.1 hs))
    rw [sumR2_eq, Nat.mul_eq] at h'
    exact h'
  have ht : ∀ i, 52136 ≤ i → ccX i = 0 := fun i hi => ccF_ge hi
  have ec : ∑ k ∈ Finset.range 52136,
      ccF ZT ccA (stepF 1) (invF 1) (PARf 1) (LABf 1) 52136 (stepF 2) (PARf 2) (LABf 2) (Mf 2)
        227759 100817 k = ∑ k ∈ Finset.range 52136, ccX k := by
    unfold ccX
    rw [m2]
  rw [ec, sum_range_tail (f := ccX) (T := 2048 * 26) ht (by norm_num), sum_slices,
    Finset.sum_congr rfl hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem ci_val {x : Nat} (hx : x < 245520) :
    (pcomp nPts cArr (pcomp nPts zArr (pinvCand nPts cArr)))[x]! = CT (ZT (CIT x)) := by
  obtain ⟨c1, c2⟩ := ci_get x hx
  obtain ⟨z1, z2⟩ := z_get _ c2
  rw [pcomp_get' hx, pcomp_get' hx, c1, z1, (c_get _ z2).1]

theorem qt_part : memIn LStrong Data.LChain.base qArr = true ∧
    peq nPts (pcomp nPts qArr (pcomp nPts qArr (pcomp nPts qArr qArr))) (pid nPts) = true ∧
    peq nPts (pcomp nPts qArr qArr) (pid nPts) = false ∧
    allBelowN 2 (fun j => peq nPts (pcomp nPts (wordArrs Data.LWords)[j]! qArr)
      (pcomp nPts qArr (wordArrs Data.LWords)[j]!)) = true ∧
    memIn MStrong Data.MChain.base tArr = true ∧
    peq nPts tArr (pcomp nPts cArr (pcomp nPts zArr (pinvCand nPts cArr))) = true ∧
    peq nPts tArr zArr = false ∧
    allBelowN 2 (fun j => memIn MStrong Data.MChain.base (wordArrs Data.LWords)[j]!) = true := by
  refine ⟨memL (fun k hk => (q_get _ (bB_lt hk)).1) (fun k hk => (q_get _ (bB_lt hk)).2) sifts.2.1, peq_of' fun i hi => ?_,
    peq_false_of' (i := 1) (by norm_num) ?_, allBelowN_iff.2 fun j hj => peq_of' fun i hi => ?_,
    memM (fun k hk => (t_get _ (bB_lt hk)).1) (fun k hk => (t_get _ (bB_lt hk)).2) (sifts.2.2.2.2 0 (by norm_num)).1,
    peq_of' fun i hi => ?_, peq_false_of' (i := 0) (by norm_num) ?_,
    allBelowN_iff.2 fun j hj => ?_⟩
  · obtain ⟨q1, q2⟩ := q_get i hi
    obtain ⟨q3, q4⟩ := q_get _ q2
    obtain ⟨q5, q6⟩ := q_get _ q4
    rw [pcomp_get' hi, pcomp_get' hi, pcomp_get' hi, q1, q3, q5, (q_get _ q6).1, pid_get' hi,
      (tab_facts hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [pcomp_get' (by norm_num), (q_get 1 (by norm_num)).1, (q_get _ (by decide +kernel)).1,
      pid_get' (by norm_num)]
    decide +kernel
  · obtain ⟨q1, q2⟩ := q_get i hi
    obtain ⟨l1, l2⟩ := l_get hj i hi
    rw [pcomp_get' hi, pcomp_get' hi, q1, l1, (l_get hj _ q2).1, (q_get _ l2).1]
    have hf := tab_facts hi
    interval_cases j
    · exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [ci_val hi, (t_get i hi).1]
    exact (tab_facts hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [(t_get 0 (by norm_num)).1, (z_get 0 (by norm_num)).1]
    decide +kernel
  · interval_cases j
    · exact memM (G := L1T) (fun k hk => (l_get (j := 0) (by norm_num) _ (bB_lt hk)).1)
        (fun k hk => (l_get (j := 0) (by norm_num) _ (bB_lt hk)).2) sifts.2.2.1
    · exact memM (G := L2T) (fun k hk => (l_get (j := 1) (by norm_num) _ (bB_lt hk)).1)
        (fun k hk => (l_get (j := 1) (by norm_num) _ (bB_lt hk)).2)
        sifts.2.2.2.1

theorem dConj_get {j : Nat} (hj : j < 4) {x : Nat} (hx : x < 245520) :
    (dConj[j]!)[x]! = CIT (DT j (CT x)) ∧ CIT (DT j (CT x)) < 245520 := by
  have hs : (wordArrs Data.intersectionWords).size = 4 := by
    rw [wordArrs, pwords_eq, Array.size_map]
    rfl
  unfold dConj
  rw [getElem!_pos _ j (by simpa [hs] using hj), Array.getElem_map,
    ← getElem!_pos (wordArrs Data.intersectionWords) j (by rw [hs]; exact hj)]
  obtain ⟨c1, c2⟩ := c_get x hx
  obtain ⟨d1, d2⟩ := d_get hj _ c2
  obtain ⟨i1, i2⟩ := ci_get _ d2
  rw [pcomp_get' hx, pcomp_get' hx, c1, d1, i1]
  exact ⟨rfl, i2⟩

theorem qPow_get : ∀ (k : Nat) {x : Nat}, x < 245520 →
    (qPowArr k)[x]! = (QT^[k]) x ∧ (QT^[k]) x < 245520
  | 0, x, hx => ⟨pid_get' hx, hx⟩
  | k + 1, x, hx => by
    obtain ⟨e, hlt⟩ := qPow_get k hx
    unfold qPowArr
    rw [pcomp_get' hx, e, (q_get _ hlt).1, Function.iterate_succ_apply']
    exact ⟨rfl, (q_get _ hlt).2⟩

theorem cqc_get (k : Nat) {x : Nat} (hx : x < 245520) :
    (cqcArr k)[x]! = CT ((QT^[k]) (CIT x)) ∧ CT ((QT^[k]) (CIT x)) < 245520 := by
  obtain ⟨i1, i2⟩ := ci_get x hx
  obtain ⟨p1, p2⟩ := qPow_get k i2
  unfold cqcArr
  rw [pcomp_get' hx, pcomp_get' hx, i1, p1, (c_get _ p2).1]
  exact ⟨rfl, (c_get _ p2).2⟩

theorem cqc_pt (k : Nat) {j : Nat} (hj : j < 4) {x : Nat} (hx : x < 245520) :
    (pcomp nPts (cqcArr k) (wordArrs Data.intersectionWords)[j]!)[x]! =
      CT ((QT^[k]) (CIT (DT j x))) ∧
    (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr k))[x]! =
      DT j (CT ((QT^[k]) (CIT x))) := by
  obtain ⟨d1, d2⟩ := d_get hj x hx
  obtain ⟨c1, c2⟩ := cqc_get k hx
  rw [pcomp_get' hx, pcomp_get' hx, d1, (cqc_get k d2).1, c1, (d_get hj _ c2).1]
  exact ⟨rfl, rfl⟩

theorem count_2 : countBelowN 4 (fun k => allBelowN 4 fun j =>
    peq nPts (pcomp nPts (cqcArr k) (wordArrs Data.intersectionWords)[j]!)
      (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr k))) = 2 := by
  have h0 : (allBelowN 4 fun j =>
      peq nPts (pcomp nPts (cqcArr 0) (wordArrs Data.intersectionWords)[j]!)
        (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr 0))) = true := by
    refine allBelowN_iff.2 fun j hj => peq_of' fun x hx => ?_
    obtain ⟨e1, e2⟩ := cqc_pt 0 hj hx
    rw [e1, e2]
    simp only [Function.iterate_zero, id]
    rw [(c_CI (d_get hj x hx).2).1, (c_CI hx).1]
  have h2 : (allBelowN 4 fun j =>
      peq nPts (pcomp nPts (cqcArr 2) (wordArrs Data.intersectionWords)[j]!)
        (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr 2))) = true := by
    refine allBelowN_iff.2 fun j hj => peq_of' fun x hx => ?_
    obtain ⟨e1, e2⟩ := cqc_pt 2 hj hx
    rw [e1, e2]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    have hd := (d_get hj x hx).2
    rw [← (tab_facts hd).2.2.2.2.2.2.2.2.2.2.2.2.1, ← (tab_facts hx).2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact (tab_facts hx).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
  have h1 : (allBelowN 4 fun j =>
      peq nPts (pcomp nPts (cqcArr 1) (wordArrs Data.intersectionWords)[j]!)
        (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr 1))) = false := by
    rw [Bool.eq_false_iff]
    intro h
    have h' := allBelowN_iff.1 h 1 (by norm_num)
    rw [peq_false_of' (i := 0) (by norm_num)] at h'
    · exact absurd h' (by decide)
    · obtain ⟨e1, e2⟩ := cqc_pt 1 (j := 1) (by norm_num) (x := 0) (by norm_num)
      rw [e1, e2]
      decide +kernel
  have h3 : (allBelowN 4 fun j =>
      peq nPts (pcomp nPts (cqcArr 3) (wordArrs Data.intersectionWords)[j]!)
        (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr 3))) = false := by
    rw [Bool.eq_false_iff]
    intro h
    have h' := allBelowN_iff.1 h 1 (by norm_num)
    rw [peq_false_of' (i := 0) (by norm_num)] at h'
    · exact absurd h' (by decide)
    · obtain ⟨e1, e2⟩ := cqc_pt 3 (j := 1) (by norm_num) (x := 0) (by norm_num)
      rw [e1, e2]
      decide +kernel
  unfold countBelowN
  have e4 : List.range 4 = [0, 1, 2, 3] := rfl
  rw [e4]
  simp only [List.filter, h0, h1, h2, h3, List.length]

theorem d0_part : allBelowN 4 (fun j => memIn MStrong Data.MChain.base
      (wordArrs Data.intersectionWords)[j]!) = true ∧
    allBelowN 4 (fun j => memIn MStrong Data.MChain.base dConj[j]!) = true ∧
    allBelowN 4 (fun j => blockImgOK dConj[j]! Data.quotientBlocks
      Data.D120Generators[j]!) = true ∧
    countBelowN 4 (fun k => allBelowN 4 fun j =>
      peq nPts (pcomp nPts (cqcArr k) (wordArrs Data.intersectionWords)[j]!)
        (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr k))) = 2 := by
  refine ⟨allBelowN_iff.2 fun j hj => ?_, allBelowN_iff.2 fun j hj => ?_,
    allBelowN_iff.2 fun j hj => ?_, count_2⟩
  · exact memM (G := DT j) (fun k hk => (d_get hj _ (bB_lt hk)).1) (fun k hk => (d_get hj _ (bB_lt hk)).2)
      (sifts.2.2.2.2 j hj).1
  · exact memM (G := fun x => CIT (DT j (CT x))) (fun k hk => (dConj_get hj (bB_lt hk)).1)
      (fun k hk => (dConj_get hj (bB_lt hk)).2)
      (sifts.2.2.2.2 j hj).2
  · refine blockImg_of (G := fun x => CIT (DT j (CT x))) (fun y hy => (dConj_get hj hy).1) ?_
    interval_cases j
    · quickRfl
    · quickRfl
    · quickRfl
    · quickRfl

theorem facts2211 :
    (peq nPts (pcomp nPts zArr zArr) (pid nPts) = true ∧ peq nPts zArr (pid nPts) = false ∧
      memIn TStrong Data.TChain.base zArr = true ∧ fixCount nPts zArr = 240 ∧ zArr[0]! = 0 ∧
      allBelowN 3 (fun j => peq nPts (pcomp nPts (wordArrs Data.MWords)[j]! zArr)
        (pcomp nPts zArr (wordArrs Data.MWords)[j]!)) = true)
    ∧ (commCount (cLevels nPts Data.baseList.toArray
        (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray))
      (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray) 1 2 zArr
      #[0, 227759, 100817] = 672)
    ∧ (pointsOK nPts Data.TPoints rPos = true ∧
      allBelowN 6 (fun j => restrictOK (wordArrs Data.TWords)[j]! Data.TPoints
        (rTab (wordArrs Data.TWords)[j]!)) = true ∧
      restrictOK zArr Data.TPoints Data.T32z = true ∧
      coversOK 32 ((wordArrs Data.TWords).map rTab) Data.T32Chain.generators = true ∧
      coversOK 32 Data.T32Chain.generators ((wordArrs Data.TWords).map rTab) = true)
    ∧ (blocksOK nPts Data.quotientBlocks bPos = true ∧
      allBelowN 3 (fun j => blockImgOK (wordArrs Data.MWords)[j]! Data.quotientBlocks
        (bTab (wordArrs Data.MWords)[j]!)) = true ∧
      allBelowN 2 (fun j => blockImgOK (wordArrs Data.LWords)[j]! Data.quotientBlocks
        (bTab (wordArrs Data.LWords)[j]!)) = true ∧
      coversOK 120 ((wordArrs Data.MWords).map bTab) Data.M120Chain.generators = true ∧
      coversOK 120 Data.M120Chain.generators ((wordArrs Data.MWords).map bTab) = true ∧
      coversOK 120 ((wordArrs Data.LWords).map bTab) Data.L120Chain.generators = true ∧
      coversOK 120 Data.L120Chain.generators ((wordArrs Data.LWords).map bTab) = true ∧
      blockImgOK qArr Data.quotientBlocks (pid 120) = true)
    ∧ (memIn LStrong Data.LChain.base qArr = true ∧
      peq nPts (pcomp nPts qArr (pcomp nPts qArr (pcomp nPts qArr qArr))) (pid nPts) = true ∧
      peq nPts (pcomp nPts qArr qArr) (pid nPts) = false ∧
      allBelowN 2 (fun j => peq nPts (pcomp nPts (wordArrs Data.LWords)[j]! qArr)
        (pcomp nPts qArr (wordArrs Data.LWords)[j]!)) = true ∧
      memIn MStrong Data.MChain.base tArr = true ∧
      peq nPts tArr (pcomp nPts cArr (pcomp nPts zArr (pinvCand nPts cArr))) = true ∧
      peq nPts tArr zArr = false ∧
      allBelowN 2 (fun j => memIn MStrong Data.MChain.base (wordArrs Data.LWords)[j]!) = true)
    ∧ (allBelowN 4 (fun j => memIn MStrong Data.MChain.base
        (wordArrs Data.intersectionWords)[j]!) = true ∧
      allBelowN 4 (fun j => memIn MStrong Data.MChain.base dConj[j]!) = true ∧
      allBelowN 4 (fun j => blockImgOK dConj[j]! Data.quotientBlocks
        Data.D120Generators[j]!) = true ∧
      countBelowN 4 (fun k => allBelowN 4 fun j =>
        peq nPts (pcomp nPts (cqcArr k) (wordArrs Data.intersectionWords)[j]!)
          (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr k))) = 2)
    ∧ (pisInv 120 Data.quotientConjugator (pinvCand 120 Data.quotientConjugator) = true ∧
      allBelowN 2 (fun j => memFull 120
        (cLevels 120 Data.PSL120Chain.base (allSteps Data.PSL120Chain.strongGenerators
          (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base))
        (allInvSteps Data.PSL120Chain.strongGenerators
          (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base)
        Data.PSL120Chain.base (pcomp 120 Data.quotientConjugator
          (pcomp 120 (bTab (wordArrs Data.LWords)[j]!)
            (pinvCand 120 Data.quotientConjugator)))) = true) :=
  ⟨z_part, comm_part, r_facts, block_facts, qt_part, d0_part, u_facts⟩

end CertificateChecks.KernelSpor.ON3

end
