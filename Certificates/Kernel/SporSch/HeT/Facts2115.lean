
module

public import Certificates.Kernel.SporSch.HeT.CntGlue
public import Certificates.Kernel.SporSch.HeT.CntA
public import Certificates.Kernel.SporSch.HeT.CntT
public import Certificates.Kernel.SporSch.HeT.CntS0
public import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeF15

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Sporadic.HeldB.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.HeO16 CertificateChecks.KernelSporSch.HeCn

theorem kT1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) HeC.S HeC.SI 2 heT1Word T1 = true := by
  quickRfl
theorem kT1c : canonK 8330 14 (mask 14) (8330 * 14) T1 = true := by quickRfl
theorem kT1C : Nat.beq (pcomp 8330 14 (mask 14) (HeC.S 1) (pcomp 8330 14 (mask 14) T1 (HeC.SI 1)))
    T1C = true := by quickRfl
theorem kFix : Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 T1) 42 = true := by quickRfl
theorem kT1C0 : Nat.beq (pm T1C 0) 0 = true := by quickRfl
theorem kA0 : Nat.beq (pm (HeC.S 0) 0) 0 = true := by quickRfl
theorem kXA : permOK 8330 14 (mask 14) (8330 * 14) XA XAI = true := by quickRfl
theorem kXT : permOK 8330 14 (mask 14) (8330 * 14) XT XTI = true := by quickRfl
theorem kXA01 : bAnd(Nat.beq (pmR HeCnRXA 0) 0, Nat.beq (pmR HeCnRXA 1) 2) = true := by quickRfl
theorem kXT01 : bAnd(Nat.beq (pmR HeCnRXT 0) 0, Nat.beq (pmR HeCnRXT 1) 2) = true := by quickRfl
theorem kRXA : rbAll HeCnRXA XA = true := by quickRfl
theorem kRYA : rbAll HeCnRYA (HeC.S 0) = true := by quickRfl
theorem kRXT : rbAll HeCnRXT XT = true := by quickRfl
theorem kRYT : rbAll HeCnRYT T1C = true := by quickRfl
theorem kFA : nfValidK 5 HeC.LR FA = true := by quickRfl
theorem kFT : nfValidK 5 HeC.LR FT = true := by quickRfl
theorem kVA : Nat.beq (sumN 8330 VA) 161280 = true := by quickRfl
theorem kVT : Nat.beq (sumN 8330 VT) 21504 = true := by quickRfl
theorem kS0 : Nat.beq (sumN 35 S0) 1984 = true := by quickRfl

theorem canonSI (j : Nat) (hj : j < 9) :
    canonK 8330 14 (mask 14) (8330 * 14) (HeC.SI j) = true :=
  ((bAnd_iff (canonK 8330 14 (mask 14) (8330 * 14) (HeC.S j))
    (canonK 8330 14 (mask 14) (8330 * 14) (HeC.SI j))).1 (allN_spec He2112.canonOK j hj)).2

theorem T1_eq : heT1Arr = unpack 8330 14 T1 ∧ lettersOK 2 heT1Word = true := by
  have hS : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (HeC.S j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    rw [heABArrs]
    interval_cases j
    · rw [arr2_get0]
      exact gen_eq 0 (by norm_num)
    · rw [arr2_get1]
      exact gen_eq 1 (by norm_num)
  exact wordEqK_sound hS (allN_of_forall fun j hj => allN_spec He2112.perm j (by omega)) kT1

theorem T1C_eq : heT1cArr = unpack 8330 14 T1C := by
  rw [heT1cArr, gen_eq 1 (by norm_num), T1_eq.1,
    (invEqK_sound (allN_spec He2112.perm 1 (by norm_num))).1, compA_unpack kT1c (canonSI 1 (by norm_num)),
    compA_unpack (canonS 1 (by norm_num)) (canonK_pcomp kT1c (canonSI 1 (by norm_num))),
    Nat.eq_of_beq_eq_true kT1C]

theorem rep_heT1' : Rep 8330 heT1Arr heT1P := by
  have hw : lettersOK [heGenPerm 0, heGenPerm 1].length heT1Word = true := T1_eq.2
  rw [heT1Arr, heT1P]
  exact rep_wordA_evalSignedWord (gs := [heGenPerm 0, heGenPerm 1]) (S := heABArrs)
    (Sinv := heABArrs.map (invCand 8330)) (fun h hh => (rep_heAB h hh).1)
    (fun h hh => (rep_heAB h hh).2) hw

theorem rep_heT1c' : Rep 8330 heT1cArr heT1cP := by
  rw [heT1cP, mul_assoc]
  exact rep_compA (rep_heGen (by norm_num)) (rep_compA rep_heT1' (rep_heGen_inv (by norm_num)))

theorem repA : RepF 8330 (pm (HeC.S 0)) (heGenPerm 0) := by
  have h := rep_heGen (k := 0) (by norm_num)
  rw [gen_eq 0 (by norm_num)] at h
  exact repF_of_rep h

theorem repT : RepF 8330 (pm T1C) heT1cP := by
  have h := rep_heT1c'
  rw [T1C_eq] at h
  exact repF_of_rep h

theorem gen0_fix0 : (heGen 0)[0]! = 0 := by
  rw [gen_eq 0 (by norm_num), unpackGet (by norm_num)]
  exact Nat.eq_of_beq_eq_true kA0

theorem t1c_fix0 : heT1cArr[0]! = 0 := by
  rw [T1C_eq, unpackGet (by norm_num)]
  exact Nat.eq_of_beq_eq_true kT1C0

theorem cardA : Nat.card {x : heP // heGenPerm 0 * (x : Equiv.Perm (Fin 8330)) = x * heGenPerm 0} =
    161280 := by
  have hX := repF_of_rb kRXA (rep_pm kXA)
  have hY := repF_of_rb kRYA repA
  have hc : ∀ s < 49, cjB HeCnRXA HeCnRYA FA s = true := CA.all
  rw [cent_of_or hX hY kFA hc (Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (pmR HeCnRXA 0) 0) (Nat.beq (pmR HeCnRXA 1) 2)).1 kXA01).1)
    (Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (pmR HeCnRXA 0) 0) (Nat.beq (pmR HeCnRXA 1) 2)).1 kXA01).2)
    (hxy_of_mem hX hY kFA hc (heGenPerm_mem (by norm_num)))
    (e := 598) (fun _ => srchAAt_eq_zero (m := 16) (c := 280) rfl fun i hi => Nat.eq_of_beq_eq_true (AH.all i hi))
    OA.all]
  exact Nat.eq_of_beq_eq_true kVA

theorem cardT : Nat.card {x : heP // heT1cP * (x : Equiv.Perm (Fin 8330)) = x * heT1cP} =
    21504 := by
  have hX := repF_of_rb kRXT (rep_pm kXT)
  have hY := repF_of_rb kRYT repT
  have hc : ∀ s < 49, cjB HeCnRXT HeCnRYT FT s = true := CT.all
  rw [cent_of_or hX hY kFT hc (Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (pmR HeCnRXT 0) 0) (Nat.beq (pmR HeCnRXT 1) 2)).1 kXT01).1)
    (Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (pmR HeCnRXT 0) 0) (Nat.beq (pmR HeCnRXT 1) 2)).1 kXT01).2)
    (hxy_of_mem hX hY kFT hc heT1cP_mem) (e := 8330) (fun h => absurd h (by norm_num)) OT.all]
  exact Nat.eq_of_beq_eq_true kVT

theorem cardS : Nat.card {x : heP // (x : Equiv.Perm (Fin 8330)) ^ 2 = 1 ∧
    (x : Equiv.Perm (Fin 8330)) 0 = 0} = 1984 := by
  have h := tw_of_cnt (U := fun b => b) (u := 1) RepF.one
    (fun g hg => by rw [one_mul]; exact heP.pow_mem hg 2) SS0.all
  rw [Nat.eq_of_beq_eq_true kS0] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [one_mul])

theorem blocks :
    (countWPar 87 (commB (heGen 0) heBase)
      (heBlock0.filter fun t0 => (heGen 0)[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 161280 &&
    countWPar 11 (commB heT1cArr heBase)
      (heBlock0.filter fun t0 => heT1cArr[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 21504 &&
    countWPar 1 (twistInvB (idA 8330) heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
      [heBlock1, heBlock2] == 1984) = true := by
  have hA := (card_heP_eq_count_filter (f := commB (heGen 0) heBase) (g := commB (heGen 0) heBase)
    (fun x => heGenPerm 0 * x = x * heGenPerm 0) _ (sz := 87) (by norm_num)
    (fun w x hw hx => commB_iff_heP (rep_heGen (by norm_num)) (heGenPerm_mem (by norm_num)) hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune gen0_fix0 (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardA
  have hT := (card_heP_eq_count_filter (f := commB heT1cArr heBase) (g := commB heT1cArr heBase)
    (fun x => heT1cP * x = x * heT1cP) _ (sz := 11) (by norm_num)
    (fun w x hw hx => commB_iff_heP rep_heT1c' heT1cP_mem hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune t1c_fix0 (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardT
  have hS := (card_heP_eq_count_filter (f := twistInvB (idA 8330) heBase)
    (g := fun w => twistInvB (idA 8330) heBase w && (evR w 0 == 0))
    (fun x => x ^ 2 = 1 ∧ x 0 = 0) _ (sz := 1) (by norm_num)
    (fun w x hw hx => by
      have h := twistInvB_iff heP_baseFaithful (rep_idA (n := 8330)) hw heBase_lt
        (by rw [one_mul]; exact heP.pow_mem hx 2)
      rw [one_mul] at h
      rw [Bool.and_eq_true, h, evR_zero_iff hw])
    fun t0 _ t1 h1 t2 h2 => zero_prune _ (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardS
  rw [hA, hT, hS]
  rfl

theorem facts : ((List.range 8330).countP (fun i => heT1Arr[i]! == i) = 42)
    ∧ (heT1cArr[0]! = 0)
    ∧ ((countWPar 87 (commB (heGen 0) heBase)
        (heBlock0.filter fun t0 => (heGen 0)[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 161280 &&
      countWPar 11 (commB heT1cArr heBase)
        (heBlock0.filter fun t0 => heT1cArr[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 21504 &&
      countWPar 1 (twistInvB (idA 8330) heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 1984) = true) := by
  refine ⟨?_, t1c_fix0, blocks⟩
  rw [T1_eq.1, CFSG.KC.HeFixK.countP_fix]
  exact Nat.eq_of_beq_eq_true kFix

end CertificateChecks.KernelSporSch.HeF15

end
