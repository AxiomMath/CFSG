module

public import CFSG.Quasithin.H13.L32NS7Inputs
import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

theorem s7_basicB_true : s7BasicB = true := by
  simp only [s7BasicB, s7E, subB, closedB, nodupB_toP, elemsOf_toF, hs_contains_toLR',
    contains_toLR, mul8_toF]
  decide +kernel

theorem s7_pB_true : CFSG.Quasithin.H13.S7Cert.pB = true := by
  simp only [CFSG.Quasithin.H13.S7Cert.pB, s7E, subB, closedB, nodupB_toP, elemsOf_toF,
    hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem s7_cvB_true : cvB = true := by
  simp only [cvB, cvE, invCv, s7E, subB, closedB, nodupB_toP, elemsOf_toF, hs_contains_toLR',
    contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

theorem s7_eWB_true : eWB = true := by
  simp only [eWB, elemsOf_toF, hs_contains_toLR', mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem s7_oB_true : CFSG.Quasithin.H13.S7Cert.oB = true := by
  simp only [CFSG.Quasithin.H13.S7Cert.oB, oE, mE, oddOf, twoOf, pow4, eSpan, subB, closedB,
    nodupB_toP, elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

set_option maxHeartbeats 0 in
theorem s7_m12B_true : CFSG.Quasithin.H13.S7Cert.m12B = true := by
  simp only [CFSG.Quasithin.H13.S7Cert.m12B, m12E, blkPerm, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', contains_toLR, mul8_toF, mv8_toR]
  decide +kernel

end CertificateChecks.KernelH13

end
