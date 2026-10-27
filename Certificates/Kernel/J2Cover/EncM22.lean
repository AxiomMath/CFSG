module

public import Certificates.Kernel.J2Cover.EncRep
public import Certificates.Kernel.J2Cover.M22Out
public import Certificates.Kernel.J2Cover.K20D
public import Certificates.Kernel.J2Cover.K20F
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

section M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Models CFSG.KC.J2Cover
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Co2 (allLt_iff)

theorem csCE : cosetCheck = true := by
  unfold cosetCheck
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun j hj => ?_
  obtain ⟨h1, h2, h3⟩ := cs_facts i hi j hj
  rw [act_pt, wit_pt, repArrs_eqE i hi, letter_eq, eltArrs_eq _ h2, repArrs_eqE _ h1,
    compA_unpackN (repT_canon i hi) (letP_canon j), compA_unpackN (eltT_canon _ h2) (repT_canon _ h1),
    eqA_unpackN (canon_pcN (repT_canon i hi) (letP_canon j))
      (canon_pcN (eltT_canon _ h2) (repT_canon _ h1)), h3, Nat.beq_refl]
  simp [h1, h2]

theorem sdCE : sDecompCheck = true := by
  unfold sDecompCheck
  refine allLt_iff.2 fun i hi => allLt_iff.2 fun a ha => ?_
  obtain ⟨h1, h2, h3⟩ := dec_facts i hi a ha
  have ep : pTab i a = pg 7 (mask 7) (DP a) i := by
    rw [pT_pt]
    unfold pK
    rw [blt_true ha]
  have ei : iTab i a = pg 13 (mask 13) (DI a) i := by
    rw [iT_pt]
    unfold iK
    rw [blt_true ha]
  rw [ep, ei, repArrs_eqE i hi, eltArrs_eq a ha, eltArrs_eq _ h1, repArrs_eqE _ h2,
    compA_unpackN (repT_canon i hi) (eltT_canon a ha), compA_unpackN (eltT_canon _ h1) (repT_canon _ h2),
    eqA_unpackN (canon_pcN (repT_canon i hi) (eltT_canon a ha))
      (canon_pcN (eltT_canon _ h1) (repT_canon _ h2)), h3, Nat.beq_refl]
  simp [h1, h2]

theorem outCE : outerCheck = true := by
  have p1 : isInvA 315 outerU outerU = true := by
    rw [hOUM]
    exact (invEqK_sound (n := 315) (w := 9) (p := OU) (r := OU) (by quickRfl)).2
  have p2 : isInvA 315 (letterArr 1) bInvArr = true := by
    have e : letterArr 1 = unpack 315 9 (PA.S 1) := letter_eq 1
    unfold bInvArr
    rw [e, (invEqK_sound (allN_spec perm 1 (by omega))).1]
    exact (invEqK_sound (allN_spec perm 1 (by omega))).2
  have p3 : eqA 315 (compA 315 bArr (compA 315 (letterArr 0) bArr)) repArrs[14]! = true := by
    rw [bArr_eq, letter_eq, repArrs_eqE 14 (by norm_num), compA_unpackN (letP_canon 0) cBB,
      compA_unpackN cBB (canon_pcN (letP_canon 0) cBB),
      eqA_unpackN (canon_pcN cBB (canon_pcN (letP_canon 0) cBB)) (repT_canon 14 (by norm_num))]
    quickRfl
  have p4 : eqA 315 (compA 315 bArr (compA 315 (letterArr 1) bArr)) repArrs[5]! = true := by
    rw [bArr_eq, letter_eq, repArrs_eqE 5 (by norm_num), compA_unpackN (letP_canon 1) cBB,
      compA_unpackN cBB (canon_pcN (letP_canon 1) cBB),
      eqA_unpackN (canon_pcN cBB (canon_pcN (letP_canon 1) cBB)) (repT_canon 5 (by norm_num))]
    quickRfl
  have p5 : allLt 128 (fun a => decide (betaIdx a < 128) &&
      eqA 315 (compA 315 bArr (compA 315 eltArrs[a]! bArr)) eltArrs[betaIdx a]!) = true := by
    refine allLt_iff.2 fun a ha => ?_
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kO5 a ha)
    have hb : betaIdx a < 128 := Nat.le_of_ble_eq_true h1
    rw [bArr_eq, eltArrs_eq a ha, eltArrs_eq _ hb, compA_unpackN (eltT_canon a ha) cBB,
      compA_unpackN cBB (canon_pcN (eltT_canon a ha) cBB),
      eqA_unpackN (canon_pcN cBB (canon_pcN (eltT_canon a ha) cBB)) (eltT_canon _ hb), h2]
    simp [hb]
  have p6 : allLt 4725 (fun i => decide (sigmaT[i]! < 4725) && decide (aCoefT[i]! < 128) &&
      eqA 315 (compA 315 bArr (compA 315 repArrs[i]! bArr))
        (compA 315 eltArrs[aCoefT[i]!]! repArrs[sigmaT[i]!]!)) = true := by
    refine allLt_iff.2 fun i hi => ?_
    have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ORB.all i hi
    unfold fOR at h
    rw [strictB_eq', strictB_eq'] at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
    have hs : pg 13 (mask 13) SGP i < 4725 := Nat.le_of_ble_eq_true h1
    have hc : pg 13 (mask 13) ACP i < 128 := Nat.le_of_ble_eq_true h2
    rw [sigmaT_eq, aCoefT_eq, getElem!_unpack hi, getElem!_unpack hi, bArr_eq, repArrs_eqE i hi,
      eltArrs_eq _ hc, repArrs_eqE _ hs, compA_unpackN (repT_canon i hi) cBB,
      compA_unpackN cBB (canon_pcN (repT_canon i hi) cBB),
      compA_unpackN (eltT_canon _ hc) (repT_canon _ hs),
      eqA_unpackN (canon_pcN cBB (canon_pcN (repT_canon i hi) cBB))
        (canon_pcN (eltT_canon _ hc) (repT_canon _ hs)), h3]
    simp [hs, hc]
  have p7 : allLt 4725 (fun i => i == 0 || i == 17 || i == 20 || iTab i 1 != i || iTab i 2 != i ||
      iTab i 3 != i) = true := by
    rw [iT_eq, allLt_eq_allN]
    exact kO7
  have p8 : [0, 17, 20].all (fun i => allLt 128 fun k =>
      !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[i]!))) = true := by
    have one : ∀ r < 3, allLt 128 (fun k =>
        !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] r]!))) = true := by
      intro r hr
      have hi : nth 0 [0, 17, 20] r < 4725 := by
        interval_cases r <;> decide
      refine allLt_iff.2 fun k hk => ?_
      rw [bArr_eq, eltArrs_eq k hk, repArrs_eqE _ hi,
        compA_unpackN (eltT_canon k hk) (repT_canon _ hi),
        eqA_unpackN cBB (canon_pcN (eltT_canon k hk) (repT_canon _ hi))]
      exact allN_spec (allN_spec kO8 r hr) k hk
    have e : [0, 17, 20].all (fun i => allLt 128 fun k =>
        !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[i]!))) =
        (allLt 128 (fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] 0]!))) &&
        (allLt 128 (fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] 1]!))) &&
        (allLt 128 (fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[nth 0 [0, 17, 20] 2]!))) &&
          true))) := rfl
    rw [e, one 0 (by omega), one 1 (by omega), one 2 (by omega)]
    rfl
  unfold outerCheck
  rw [p1, p2, p3, p4, p5, p6, p7, p8]
  rfl

end M22

section K20D

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.ComponentClassification.J2Cover.External (fusionP fusionI fusionArr lamCheck fusionBit)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem lamPartE : allLt 4725 (fun i => decide (fusionP[i]! < 128) &&
    decide (fusionI[i]! < 4725) && eqA 315 (compA 315 repArrs[i]! fusionArr)
      (compA 315 eltArrs[fusionP[i]!]! repArrs[fusionI[i]!]!)) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) LMB.all i hi
  unfold lamTK at h
  rw [strictB_eq', strictB_eq'] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  have hp := Nat.le_of_ble_eq_true h1
  have hq := Nat.le_of_ble_eq_true h2
  rw [fusionP_eq, fusionI_eq, getElem!_unpack hi, getElem!_unpack hi, repArrs_eqE i hi, hFU,
    eltArrs_eq _ hp, repArrs_eqE _ hq, compA_unpackN (repT_canon i hi) cFU,
    compA_unpackN (eltT_canon _ hp) (repT_canon _ hq),
    eqA_unpackN (canon_pcN (repT_canon i hi) cFU) (canon_pcN (eltT_canon _ hp) (repT_canon _ hq)),
    h3]
  simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp, hq⟩

theorem lamCE : lamCheck = true := by
  unfold lamCheck
  rw [lamPartE, xorPart]
  rfl

end K20D

end CertificateChecks.KernelJ2Cover

end
