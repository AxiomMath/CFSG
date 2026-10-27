
module

public import CFSG.Monster.B.TwoA.Fischer.CertFixedInputs
public import Certificates.Kernel.MonsterB.IndCandGet
public import Certificates.Kernel.MonsterB.FischerTabs
public import CFSG.Certificates.Kernel.MonsterB.FischerKSound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMonB.Fischer3066

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Binary.Native CFSG.KC.FischerK CertificateChecks.KernelMonB.IndCand
  CertificateChecks.KernelMonB.FischerTabs

@[expose] def fTrs : List (List Nat) :=
  [fTr0, fTr1, fTr2, fTr3, fTr4, fTr5, fTr6, fTr7, fTr8, fTr9, fTr10, fTr11]

@[expose] def subOneT : List Nat :=
  (List.range 12).flatMap fun k => (List.range 78).map fun i => (fTrs[k]!).toArray[i]! ^^^ (1 <<< i)

theorem basisPt_lt : ∀ i < 78, basisPt i < 3510 := by decide +kernel

theorem kShape : fShapeCheck = true := by decide +kernel

theorem kCol : ((List.range 12).all fun k => (List.range 78).all fun i =>
    fCol k i == labelCoord (candF k (basisPt i))) = true := by decide +kernel

theorem kFix : fFixCheck = true := by decide +kernel

theorem kTr : ∀ k < 12, (transposeRows 78 (fColArr[k]!)).toList = fTrs[k]! := by decide +kernel

theorem kElim : (elimTable 78 subOneT == some fElim.toArray) = true := by decide +kernel

theorem elim_eq : elimTable 78 subOneT = some fElim.toArray := beq_iff_eq.1 kElim

theorem kBelow : allBelow 78 subOneT = true := by decide +kernel

theorem kRankT : rankOpt 78 77 (some fElim.toArray) = true := by decide +kernel

theorem kFreeT : ((List.range 78).all fun p => (fElim.toArray[p]! == 0) == [0].contains p) = true := by
  decide +kernel

theorem kRank : spanRankIs 78 subOneT 77 = true := by
  rw [spanRankIs, elim_eq, kBelow, kRankT]
  rfl

theorem kFree : freeIs 78 subOneT [0] = true := by
  rw [freeIs, elim_eq, kBelow]
  exact kFreeT

theorem kClique : spanRankIs 78 ((List.range 22).map labelCoord) 11 = true := by decide +kernel

theorem kLen : GramLit.rowCoords.length = 3510 := by decide +kernel

theorem kCoordNe : allIdx (fun _ c => c != 949 && decide (c < 2 ^ 78)) GramLit.rowCoords 0 = true := by
  decide +kernel

theorem kMask : maskSum = 949 := by decide +kernel

theorem fColCheck_true : fColCheck = true := by
  rw [← kCol]
  unfold fColCheck
  apply all_range_congr
  intro k hk
  apply all_range_congr
  intro i hi
  rw [cand_get (by omega) (basisPt_lt i hi)]

theorem subOneRows_eq : subOneRows (List.range 12) = subOneT := by
  rw [subOneRows, subOneT, List.flatMap_def, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun k hk => ?_)
  have h := kTr k (List.mem_range.1 hk)
  have h' : transposeRows 78 (fColArr[k]!) = (fTrs[k]!).toArray := by
    rw [← h, Array.toArray_toList]
  rw [h']

theorem coordNeCheck_true : coordNeCheck = true := by
  unfold coordNeCheck
  rw [← kLen]
  exact (range_all_eq_allIdx (fun _ c => c != 949 && decide (c < 2 ^ 78)) GramLit.rowCoords).trans
    kCoordNe

theorem facts : (fShapeCheck = true) ∧ (fColCheck = true) ∧ (fFixCheck = true)
    ∧ (spanRankIs 78 (subOneRows (List.range 12)) 77 = true)
    ∧ (freeIs 78 (subOneRows (List.range 12)) [0] = true)
    ∧ (spanRankIs 78 ((List.range 22).map labelCoord) 11 = true)
    ∧ (coordNeCheck = true) ∧ (maskSum = 949) := by
  rw [subOneRows_eq]
  exact ⟨kShape, fColCheck_true, kFix, kRank, kFree, kClique, coordNeCheck_true, kMask⟩

end CertificateChecks.KernelMonB.Fischer3066

end
