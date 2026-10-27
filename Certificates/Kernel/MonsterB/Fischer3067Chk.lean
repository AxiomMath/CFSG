module

public import Certificates.Kernel.MonsterB.Fischer3067T
public import Certificates.Kernel.MonsterB.FischerTabs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Binary.Native
  CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT CertificateChecks.KernelMonB.FischerTabs

theorem kOrbB : orbBound = true := by decide +kernel

theorem kRows : rowsChk = true := by decide +kernel

theorem kTShape : (bTableArr.size == 78 && bTableArr.all (·.size == 78)) = true := by decide +kernel

theorem kTable : (List.range 78).all tableRowT = true := by decide +kernel

theorem kRad : (((List.range 22).all fun c => decide (labelCoord c < 2 ^ 11)) &&
    ((List.range 11).all fun q => decide (basisPt q < 22)) &&
    (transIdx.all fun k => (List.range 2048).all fun m => vecMulL (fColArr[k]!).toList m == m) &&
    (transIdx.all fun k => (List.range 11).all fun q => fCol k q == 2 ^ q)) = true := by
  decide +kernel

@[expose] def fTrsL : List (List Nat) :=
  [fTr0, fTr1, fTr2, fTr3, fTr4, fTr5, fTr6, fTr7, fTr8, fTr9, fTr10, fTr11]

@[expose] def subOneTr : List Nat :=
  transIdx.flatMap fun k => (List.range 78).map fun i => (fTrsL[k]!).toArray[i]! ^^^ (1 <<< i)

theorem kRank : spanT subOneTr 67 = true := by decide +kernel

theorem kFree : (allBelow 78 subOneTr && (List.range 78).all fun p =>
    ((elimL 77 subOneTr (zerosL 78)).reverse.toArray[p]! == 0) == (List.range 11).contains p) =
    true := by
  decide +kernel

theorem kRest : orbitRestT = true := by decide +kernel

theorem kCard : ∀ t < 8, ((List.range 2048).map fun m => if oIdx m = t then 1 else 0).sum =
    orbLen t := by
  decide +kernel

@[expose] def ad949cs : List (List Nat) :=
  [ad949c0, ad949c1, ad949c2, ad949c3, ad949c4, ad949c5, ad949c6, ad949c7, ad949c8, ad949c9,
    ad949c10, ad949c11, ad949c12, ad949c13, ad949c14, ad949c15, ad949c16, ad949c17, ad949c18,
    ad949c19, ad949c20, ad949c21]

theorem kAd : adL 949 = ad949 := by decide +kernel

theorem kAdc : ∀ c < 22, adL (949 ^^^ labelCoord c) = ad949cs[c]! := by decide +kernel

@[expose] noncomputable def zeroT (A : List Nat) : Bool :=
  allIdx (fun q c => decide (vecMulL A c < 2 ^ 78) && (vecMulL A c == 0) == decide (q < 22))
    GramLit.rowCoords 0

theorem kZ : zeroT ad949 = true := by decide +kernel

theorem kZc : ∀ c < 22, zeroT (ad949cs[c]!) = true := by decide +kernel

end CertificateChecks.KernelMonB.F3067

end
