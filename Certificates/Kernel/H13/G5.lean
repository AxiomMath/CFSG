module

public import CFSG.Quasithin.H13.L32NG5Inputs
import CFSG.Certificates.Kernel.Mat8PSound
public import Certificates.Kernel.H13.BlkHom
import CFSG.Certificates.Kernel.Mat8TSound
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Cert CFSG.Quasithin.H13.S8Cert
  CFSG.Quasithin.H13.G5Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

theorem g5_basicB_true : CFSG.Quasithin.H13.G5Cert.basicB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.basicB, gSE, gAE, gAG, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

theorem g5_pB_true : CFSG.Quasithin.H13.G5Cert.pB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.pB, gSE, gAE, gAG, pAG, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

theorem g5_zB_true : CFSG.Quasithin.H13.G5Cert.zB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.zB, elemsOf_toF, hs_contains_toLR', mul8_toF]
  decide +kernel

theorem g5_wB_true : CFSG.Quasithin.H13.G5Cert.wB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.wB, pAG, eSpanA, eSpanS, elemsOf_toF, hs_contains_toLR',
    mul8_toF, mv8_toR, nodupN, decide_isChain_toP]
  decide +kernel

@[expose] def g5ovF (y : List ℕ) : Bool :=
  (Std.HashSet.ofList (elemsOf pSG)).contains y ||
    (let B := elemsOf (pSG ++ [y]) 49
     (49 ≤ B.length && nodupB B) ||
       (B.length == 48 && nodupB B &&
         ([0, 1].map fun i => Std.HashSet.ofList (mES i)).any fun h => B.all h.contains))

set_option maxHeartbeats 0 in
theorem g5_ovB_eq : CFSG.Quasithin.H13.G5Cert.ovB =
    (mRepsS.length == 2 && mRepsS.all (Std.HashSet.ofList gSE).contains &&
      ([0, 1].all fun i => (mES i).length == 48 && subB (pSG ++ [mRepsS.getD i one8]) (mES i)) &&
      gSE.all g5ovF) := by
  delta CFSG.Quasithin.H13.G5Cert.ovB g5ovF
  rfl

set_option maxHeartbeats 0 in
theorem g5_ovC0 : ((gSE.drop (0 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC1 : ((gSE.drop (1 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC2 : ((gSE.drop (2 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC3 : ((gSE.drop (3 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC4 : ((gSE.drop (4 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC5 : ((gSE.drop (5 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC6 : ((gSE.drop (6 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_ovC7 : ((gSE.drop (7 * 90)).take 90).all g5ovF = true := by
  delta g5ovF
  simp only [gSE, mES, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map, Function.comp_def,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

theorem g5_ovY : gSE.all g5ovF = true := by
  apply CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 90 8
    (by simp only [gSE, CFSG.KC.Mat8T.elemsOf_T]; decide +kernel)
  intro j hj
  interval_cases j
  · exact g5_ovC0
  · exact g5_ovC1
  · exact g5_ovC2
  · exact g5_ovC3
  · exact g5_ovC4
  · exact g5_ovC5
  · exact g5_ovC6
  · exact g5_ovC7

set_option maxHeartbeats 0 in
theorem g5_ovB_true : CFSG.Quasithin.H13.G5Cert.ovB = true := by
  rw [g5_ovB_eq, g5_ovY, Bool.and_true]
  simp only [gSE, mES, subB, closedB, nodupB_toP, CFSG.KC.Mat8T.elemsOf_T, List.any_map,
    Function.comp_def, hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

theorem g5_oB_true : CFSG.Quasithin.H13.G5Cert.oB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.oB, oES, mES, oddOf, twoOf, pow4, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

theorem g5_m12ES_bpOK : m12ES.all (fun x => bpOK blkSA x && bpOK blkSB x) = true := by
  simp only [m12ES, bpOK, elemsOf_toF, mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_m12B_true : CFSG.Quasithin.H13.G5Cert.m12B = true := by
  rw [CFSG.Quasithin.H13.G5Cert.m12B, pairs_of_bpOK m12ES blkSA blkSB
    (valid8_elemsOf _ (by simp only [Valid8]; decide) _) g5_m12ES_bpOK, Bool.and_true]
  simp only [m12ES, blkPerm, subB, closedB, nodupB_toP, elemsOf_toF, hs_contains_toLR',
    contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

theorem g5Check_true : g5Check = true := by
  rw [g5Check, g5_basicB_true, g5_pB_true, g5_zB_true, g5_wB_true, g5_ovB_true, g5_oB_true,
    g5_m12B_true]
  rfl

end CertificateChecks.KernelH13

end
