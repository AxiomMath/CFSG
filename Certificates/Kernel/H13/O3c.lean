module

public import CFSG.Quasithin.H13.L32NO3cInputs
import Certificates.Kernel.H13.ElemsO3
public import Mathlib

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.Quasithin.H13.O3cCert
  CFSG.KC.Mat8P

macro "o3c_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H13.O3cCert.p0B, CFSG.Quasithin.H13.O3cCert.c4B,
    CFSG.Quasithin.H13.O3cCert.c5B, CFSG.Quasithin.H13.O3cCert.p0E,
    CertificateChecks.KernelH13.om3E_eq, CertificateChecks.KernelH13.om3FE_eq,
    CertificateChecks.KernelH13.omNE_eq, CFSG.Quasithin.H13.Mat8Cert.subB,
    CFSG.Quasithin.H13.Mat8Cert.closedB, CFSG.KC.Mat8P.nodupB_toP, CFSG.KC.Mat8P.elemsOf_toF,
    CFSG.Quasithin.H13.O3Cert.fullImgB, CFSG.Quasithin.H13.O3Cert.imgBasis,
    CFSG.KC.Mat8P.decide_isChain_toP, CFSG.Quasithin.H13.G5Cert.quadN,
    CFSG.KC.Mat8P.hs_contains_toLR', CFSG.KC.Mat8P.hs_contains_toLR,
    CFSG.KC.Mat8P.contains_toLR, CFSG.KC.Mat8P.mul8_toF, CFSG.KC.Mat8P.mv8_toR]
  decide +kernel))

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem o3c_p0B_true : p0B = true := by o3c_tac

set_option maxHeartbeats 0 in
theorem o3c_c4B_true : c4B = true := by o3c_tac

set_option maxHeartbeats 0 in
theorem o3c_c5B_true : c5B = true := by o3c_tac

theorem o3cCheck_true : o3cCheck = true := by
  rw [o3cCheck, o3c_p0B_true, o3c_c4B_true, o3c_c5B_true]
  rfl

end CertificateChecks.KernelH13

end
