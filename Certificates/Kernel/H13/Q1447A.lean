module

public import CFSG.Quasithin.H13.L32N1447AInputs
import Certificates.Kernel.H13.Pow

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.G5Cert CFSG.Quasithin.H13.G5ACert
  CFSG.Quasithin.H13.Q1447Cert CFSG.Quasithin.H13.Q1447A CFSG.KC.Mat8P

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem q1447a_a5InvB_true : a5InvB = true := by
  simp only [a5InvB, gEA, gSAE, gAAE, invol8, b5A, quadA, elemsOf_toF, mul8_toF, mv8_toR]
  decide +kernel

theorem q1447a_a5PB_true : a5PB = true := by
  simp only [a5PB, pEA, invol8, bigImg8, CFSG.Quasithin.H13.O3Cert.imgBasis, elemsOf_toF,
    mul8_toF, mv8_toR, decide_isChain_toP]
  decide +kernel

theorem q1447a_a5ZB_true : a5ZB = true := by
  simp only [a5ZB, pEA, elemsOf_toF, contains_toLR, mul8_toF]
  decide +kernel

set_option maxHeartbeats 0 in
theorem q1447a_a5KB_true : a5KB = true := by
  simp only [a5KB, CFSG.Quasithin.H13.Q1447Cert.conjB, conjOf, gEA, gSAE, gAAE, subB, closedB, nodupB_toP,
    elemsOf_toF, hs_contains_toLR', hs_contains_toLR, contains_toLR, mul8_toF, pow8_toF]
  decide +kernel

theorem q1447aCheck_true : q1447aCheck = true := by
  rw [q1447aCheck, q1447a_a5InvB_true, q1447a_a5PB_true, q1447a_a5ZB_true, q1447a_a5KB_true]
  rfl

end CertificateChecks.KernelH13

end
