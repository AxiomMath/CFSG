module

public import CFSG.Quasithin.H13.L32NG5Inputs
import CFSG.Certificates.Kernel.Mat8PSound

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

set_option maxHeartbeats 0 in
theorem g5_ovB_true : CFSG.Quasithin.H13.G5Cert.ovB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.ovB, gSE, mES, subB, closedB, nodupB_toP, elemsOf_toF,
    List.any_map, Function.comp_def, hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

theorem g5_oB_true : CFSG.Quasithin.H13.G5Cert.oB = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.oB, oES, mES, oddOf, twoOf, pow4, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5_m12B_true : CFSG.Quasithin.H13.G5Cert.m12B = true := by
  simp only [CFSG.Quasithin.H13.G5Cert.m12B, m12ES, blkPerm, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

theorem g5Check_true : g5Check = true := by
  rw [g5Check, g5_basicB_true, g5_pB_true, g5_zB_true, g5_wB_true, g5_ovB_true, g5_oB_true,
    g5_m12B_true]
  rfl

end CertificateChecks.KernelH13

end
