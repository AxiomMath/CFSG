module

public import CFSG.Quasithin.H13.L32A1410Inputs
import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Cert CFSG.Quasithin.H13.S8Cert
  CFSG.Quasithin.H13.G5Cert CFSG.Quasithin.H13.G5ACert CFSG.KC.Mat8P

set_option maxRecDepth 100000

theorem g5a_basicAB_true : basicAB = true := by
  simp only [basicAB, gEA, gSAE, gAAE, subB, closedB, nodupB_toP, elemsOf_toF,
    hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

theorem g5a_pAB_true : pAB = true := by
  simp only [pAB, gEA, gSAE, gAAE, pEA, subB, closedB, nodupB_toP, elemsOf_toF,
    hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5a_ovAB_true : ovAB = true := by
  simp only [ovAB, gEA, gSAE, gAAE, pEA, mEA, subB, closedB, nodupB_toP, elemsOf_toF,
    List.any_map, Function.comp_def, hs_contains_toLR', contains_toLR, mul8_toF]
  decide +kernel

theorem g5a_oAB_true : oAB = true := by
  simp only [oAB, oEA, mEA, oddOf, subB, closedB, nodupB_toP, elemsOf_toF, hs_contains_toLR',
    contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem g5a_kAB_true : kAB = true := by
  simp only [kAB, kAE, kAP, conjA, gEA, gSAE, gAAE, pEA, mEA, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

theorem g5aCheck_true : g5aCheck = true := by
  rw [g5aCheck, g5a_basicAB_true, g5a_pAB_true, g5a_ovAB_true, g5a_oAB_true, g5a_kAB_true]
  rfl

end CertificateChecks.KernelH13

end
