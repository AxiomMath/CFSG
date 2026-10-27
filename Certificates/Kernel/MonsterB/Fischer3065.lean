
module

public import Certificates.Kernel.MonsterB.Fischer3065Chk
public import Certificates.Kernel.MonsterB.Fischer3065W
public import Certificates.Kernel.MonsterB.FischerLabels
public import Certificates.Kernel.MonsterB.FischerHex
public import Certificates.Kernel.MonsterB.Fischer3066

public section

namespace CertificateChecks.KernelMonB.F3065

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2.Native CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT
  CertificateChecks.KernelMonB.F3067

theorem bit_testBit (X i : Nat) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, decide_eq_true_eq]

theorem ofBits_beq (d : Nat) (f : Nat → Bool) (N : Nat) :
    (ofBits d f == N) = (decide (N < 2 ^ d) && allN d fun q => f q == bit N q) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro rfl
    refine ⟨CFSG.Sporadic.SmallF2.ofBits_lt d f, allN_of fun q hq => ?_⟩
    rw [bit_testBit, CFSG.Sporadic.SmallF2.ofBits_testBit, decide_eq_true hq, Bool.true_and,
      beq_self_eq_true]
  · rintro ⟨hN, hall⟩
    apply Nat.eq_of_testBit_eq
    intro q
    rw [CFSG.Sporadic.SmallF2.ofBits_testBit]
    by_cases hq : q < d
    · have := allN_true hall q hq
      rw [beq_iff_eq, bit_testBit] at this
      rw [decide_eq_true hq, Bool.true_and, this]
    · rw [decide_eq_false hq, Bool.false_and]
      exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hN
        (Nat.pow_le_pow_right (by omega) (by omega)))).symm

theorem ofBits_congr' {d : Nat} {f g : Nat → Bool} (h : ∀ q < d, f q = g q) :
    ofBits d f = ofBits d g := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [CFSG.Sporadic.SmallF2.ofBits_testBit, CFSG.Sporadic.SmallF2.ofBits_testBit]
  by_cases hq : q < d
  · rw [h q hq]
  · simp [hq]

theorem colN_testBit (y : Nat) : ∀ (L : List Nat) (i : Nat),
    (colN L y).testBit i = (decide (i < L.length) && (L[i]?.getD 0).testBit y)
  | [], i => by
    change (0 : Nat).testBit i = _
    simp
  | r :: L, i => by
    change ((r >>> y &&& 1) ||| (colN L y <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    have ih := colN_testBit y L
    cases i with
    | zero => simp
    | succ i =>
      have h1 : Nat.testBit 1 (i + 1) = false := by
        rw [Nat.testBit_succ]
        simp
      simp [ih i, h1]

theorem ncRow_eq (i : Nat) : ncRow i = ncL i := by
  unfold ncRow ncL
  rw [CertificateChecks.KernelMonB.FischerHex.ncRowArr_eq]

theorem ofBits_colN (y : Nat) : ofBits 78 (fun i => (ncL i).testBit y) = colN GramLit.ncRows y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [CFSG.Sporadic.SmallF2.ofBits_testBit, colN_testBit, kNcLen]
  by_cases hi : i < 78
  · simp [hi, ncL, List.getElem!_toArray, List.getElem!_eq_getElem?_getD]
  · simp [hi]

theorem gramRow_ok {i : Nat} (hi : i < 78) :
    (let w := labelWord i
     let h := jWordArr w
     w.all (· < 13) && h[22]! == basisPt i && isInvA 3510 h (invCand 3510 h) &&
       supportBits (jLabelArr w) == ncRow i &&
       gramRow i == ofBits 78 (fun k => (ncRow i).testBit (basisPt k))) = true := by
  have hT : gramRowT i = true := by
    have key : ∀ s < 6, 13 * s ≤ i → i < 13 * s + 13 → gramRowT i = true := by
      intro s hs h1 h2
      have hmem : i ∈ List.range' (13 * s) 13 := List.mem_range'_1.2 ⟨h1, h2⟩
      interval_cases s
      · exact List.all_eq_true.1 kW0 i hmem
      · exact List.all_eq_true.1 kW1 i hmem
      · exact List.all_eq_true.1 kW2 i hmem
      · exact List.all_eq_true.1 kW3 i hmem
      · exact List.all_eq_true.1 kW4 i hmem
      · exact List.all_eq_true.1 kW5 i hmem
    exact key (i / 13) (by omega) (by omega) (by omega)
  unfold gramRowT at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨⟨hw, h22⟩, hs⟩, hg⟩ := hT
  have hw' : ∀ j ∈ labelWord i, j < 13 := by
    intro j hj
    have := List.all_eq_true.1 hw j hj
    simpa using this
  simp only [ncRow_eq]
  rw [hw, jWordArr_get _ hw' 22 (by omega), h22, isInvA_word hw', hg]
  have hsupp : supportBits (jLabelArr (labelWord i)) = ofBits 3510 fun q => labF (labelWord i) q != q := by
    unfold supportBits
    exact ofBits_congr' fun q hq => by rw [jLabelArr_get hw' hq]
  rw [hsupp, ofBits_beq]
  unfold suppT at hs
  rw [hs]
  rfl

theorem gramWordCheck_true : gramWordCheck = true := by
  unfold gramWordCheck
  rw [List.all_eq_true]
  intro i hi
  exact gramRow_ok (List.mem_range.1 hi)

theorem coordCheck_true : coordCheck = true := by
  have hG : transposeRows 78 gramRowArr = FD.GT.toArray := by
    rw [← Array.toArray_toList (xs := transposeRows 78 gramRowArr), kGT]
  have hs : FD.GT.toArray.size = 78 := by
    rw [← hG]
    simp [transposeRows]
  unfold coordCheck
  rw [kCoord1, Bool.true_and]
  simp only [hG, vecMulN_eq hs, List.toList_toArray, ncRow_eq, ofBits_colN]
  rw [← CertificateChecks.KernelMonB.Fischer3066.kLen]
  exact (range_all_eq_allIdx (fun y c => vecMulL FD.GT c == colN GramLit.ncRows y)
    GramLit.rowCoords).trans kCoord2

theorem facts : (gramWordCheck = true) ∧ (gramInvCheck = true) ∧ (coordCheck = true)
    ∧ ((List.range 78).map basisPt =
       [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
         39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
         94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
         535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326]) :=
  ⟨gramWordCheck_true, kInvG, coordCheck_true, kBasis⟩

end CertificateChecks.KernelMonB.F3065

end
