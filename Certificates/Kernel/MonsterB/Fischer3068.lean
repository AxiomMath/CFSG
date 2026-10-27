module

public import CFSG.Monster.B.TwoA.Fischer.CertSeedInputs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMonB.Fischer3068

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Binary.Native CFSG.KC.FischerK CertificateChecks.KernelMonB.IndCand
  CertificateChecks.KernelMonB.FischerTabs CertificateChecks.KernelMonB.Fischer3066

theorem fourGen_lt : ∀ k < 4, fourGen k < 13 := by decide +kernel

theorem kFour : (fourColArr.size == 4 && fourColArr.all (·.size == 78) &&
    (List.range 4).all fun k => (List.range 78).all fun i =>
      (fourColArr[k]!)[i]! == labelCoord (candF (fourGen k) (basisPt i))) = true := by
  decide +kernel

theorem kSeedPre : seedPre = 16058837531770935235962 := by decide +kernel

theorem kRoot : rootOpNum 949 16058837531770935235962 = 16058837527637121392057 := by
  decide +kernel

theorem kAd : (adCols 16058837527637121392057).toList = adSeed := by decide +kernel

theorem kAdLen : adSeed.length = 78 := by decide +kernel

theorem kZero : allIdx (fun q c => decide (vecMulL adSeed c < 2 ^ 78) &&
    (vecMulL adSeed c == 0) == seedLabels.contains q) GramLit.rowCoords 0 = true := by
  decide +kernel

theorem four_eq : ((List.range 4).all fun k => (List.range 78).all fun i =>
      (fourColArr[k]!)[i]! == labelCoord ((indCandidate (fourGen k))[basisPt i]!)) =
    ((List.range 4).all fun k => (List.range 78).all fun i =>
      (fourColArr[k]!)[i]! == labelCoord (candF (fourGen k) (basisPt i))) := by
  apply all_range_congr
  intro k hk
  apply all_range_congr
  intro i hi
  rw [cand_get (fourGen_lt k hk) (basisPt_lt i hi)]

theorem fourCheck_true : fourCheck = true := by
  unfold fourCheck
  rw [four_eq]
  exact kFour

theorem seedZeroCheck_true : seedZeroCheck = true := by
  have hA : adCols 16058837527637121392057 = adSeed.toArray := by
    rw [← kAd, Array.toArray_toList]
  have hs : adSeed.toArray.size = 78 := by rw [List.size_toArray, kAdLen]
  unfold seedZeroCheck
  rw [hA, ← kLen]
  simp only [vecMulN_eq hs, List.toList_toArray]
  exact (range_all_eq_allIdx (fun q c => decide (vecMulL adSeed c < 2 ^ 78) &&
    (vecMulL adSeed c == 0) == seedLabels.contains q) GramLit.rowCoords).trans kZero

theorem facts : (fourCheck = true) ∧ (seedPre = 16058837531770935235962)
    ∧ (rootOpNum 949 16058837531770935235962 = 16058837527637121392057)
    ∧ (seedZeroCheck = true) :=
  ⟨fourCheck_true, kSeedPre, kRoot, seedZeroCheck_true⟩

end CertificateChecks.KernelMonB.Fischer3068

end
