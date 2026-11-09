module

public import Certificates.Kernel.MonsterB.Fischer3067T
public import Certificates.Kernel.MonsterB.FischerTabs
public import Certificates.Kernel.MonsterB.Fischer3067ZTab
public import Certificates.Data.Kernel.MonsterB.FischerKT
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

theorem kRad1 : ((List.range 22).all fun c => decide (labelCoord c < 2 ^ 11)) = true := by
  decide +kernel

theorem kRad2 : ((List.range 11).all fun q => decide (basisPt q < 22)) = true := by
  decide +kernel

theorem kRad4 : (transIdx.all fun k => (List.range 11).all fun q => fCol k q == 2 ^ q) = true := by
  decide +kernel

theorem kPow11 : (List.range 2048).all (fun m => vecMulL pow11C m == m) = true := by
  decide +kernel

theorem kRad : (((List.range 22).all fun c => decide (labelCoord c < 2 ^ 11)) &&
    ((List.range 11).all fun q => decide (basisPt q < 22)) &&
    (transIdx.all fun k => (List.range 2048).all fun m => vecMulL (fColArr[k]!).toList m == m) &&
    (transIdx.all fun k => (List.range 11).all fun q => fCol k q == 2 ^ q)) = true := by
  have h3 : (transIdx.all fun k => (List.range 2048).all fun m =>
      vecMulL (fColArr[k]!).toList m == m) = true := by
    rw [List.all_eq_true]
    intro k hk
    rw [List.all_eq_true]
    intro m hm
    have hq : ∀ q < 11, (fColArr[k]!)[q]! = 2 ^ q := fun q hq =>
      beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 kRad4 k hk) q (List.mem_range.2 hq))
    exact beq_iff_eq.2 (vecMulL_unitC kPow11 _ hq m (List.mem_range.1 hm))
  rw [kRad1, kRad2, h3, kRad4]
  rfl

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

@[expose] noncomputable def zeroG3067 (f : Nat → Nat) : Bool :=
  allIdx (fun q c => decide (f c < 2 ^ 78) && (f c == 0) == decide (q < 22)) GramLit.rowCoords 0

theorem zeroT_of_tab {T A : List Nat} (h : chTabOK T A = true) :
    zeroT A = zeroG3067 (vecMulCT T) := by
  change zeroG3067 (vecMulL A) = zeroG3067 (vecMulCT T)
  rw [funext (vecMulCT_eq T A h)]

theorem kTab949 : chTabOK zTab949 ad949 = true := by decide +kernel

theorem kTabc : ∀ c < 22, chTabOK (zTabc[c]!) (ad949cs[c]!) = true := by decide +kernel

theorem kZT949 :zeroG3067 (vecMulCT zTab949) = true := by decide +kernel

theorem kZTall : zTabc.all (fun T => zeroG3067 (vecMulCT T)) = true := by decide +kernel

theorem kZTc : ∀ c < 22, zeroG3067 (vecMulCT (zTabc[c]!)) = true := by
  intro c hc
  have hl : c < zTabc.length := by
    have h22 : zTabc.length = 22 := rfl
    omega
  rw [getElem!_pos zTabc c hl]
  exact List.all_eq_true.1 kZTall _ (List.getElem_mem hl)

theorem kZ : zeroT ad949 = true := (zeroT_of_tab kTab949).trans kZT949

theorem kZc : ∀ c < 22, zeroT (ad949cs[c]!) = true := fun c hc =>
  (zeroT_of_tab (kTabc c hc)).trans (kZTc c hc)

end CertificateChecks.KernelMonB.F3067

end
