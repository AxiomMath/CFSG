module

public import CFSG.Quasithin.H13.L32N1449Inputs
public import Certificates.Data.Kernel.Mat8R
import Certificates.Kernel.H13.ElemsO3
import Certificates.Kernel.H13.Pow
import Certificates.Kernel.H13.Q1449InvGlue
public import Certificates.Kernel.H13.DataQ1449
import Certificates.Kernel.H13.Q1449Cen
import CFSG.Certificates.Kernel.Mat8RSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.Quasithin.H13.Q1449Cert
  CFSG.KC.Mat8P

macro "q1449_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H13.Q1449Cert.xsB, CFSG.Quasithin.H13.Q1449Cert.cPWB,
    CFSG.Quasithin.H13.Q1449Cert.alt0B, CFSG.Quasithin.H13.Q1449Cert.expB,
    CFSG.Quasithin.H13.Q1449Cert.cjB, CFSG.Quasithin.H13.Q1449Cert.x0AB,
    CFSG.Quasithin.H13.Q1449Cert.betaB, CFSG.Quasithin.H13.Q1449Cert.sigB,
    CFSG.Quasithin.H13.Q1449Cert.irrB, CFSG.Quasithin.H13.Q1449Cert.invRkB,
    CFSG.Quasithin.H13.Q1449Cert.aL, CFSG.Quasithin.H13.Q1449Cert.sigOf,
    CFSG.Quasithin.H13.Q1449Cert.o5L, CFSG.Quasithin.H13.Q1449Cert.small64B,
    CFSG.Quasithin.H13.Q1449Cert.fullAltB, CFSG.Quasithin.H13.O3Cert.gamE,
    CFSG.Quasithin.H13.O3Cert.pE, CFSG.Quasithin.H13.O3Cert.wE, CFSG.Quasithin.H13.O3Cert.cxs,
    CFSG.Quasithin.H13.O3Cert.smallImgB, CFSG.Quasithin.H13.O3Cert.imgBasis,
    CFSG.Quasithin.H13.O3Cert.fullImgB, CertificateChecks.KernelH13.om3E_eq,
    CertificateChecks.KernelH13.om3FE_eq, CertificateChecks.KernelH13.omNE_eq,
    CertificateChecks.KernelH13.h2E_eq, CFSG.Quasithin.H13.G5Cert.b5N,
    CFSG.Quasithin.H13.G5Cert.quadN, CFSG.KC.Mat8P.elemsOf_toF, CFSG.KC.Mat8P.decide_isChain_toP,
    CFSG.KC.Mat8P.hs_contains_toLR', CFSG.KC.Mat8P.hs_contains_toLR,
    CFSG.KC.Mat8P.contains_toLR, CFSG.KC.Mat8P.hsN_contains_toP',
    CFSG.KC.Mat8P.hsN_contains_toP, CFSG.KC.Mat8P.mul8_toF, CFSG.KC.Mat8P.mv8_toR,
    CertificateChecks.KernelH13.pow8_toF]
  decide +kernel))

set_option maxRecDepth 100000

@[expose] noncomputable def irrK : Bool :=
  [0, 1].all fun c => (List.range 256).all fun v =>
    (spanN (imgBasis (xsS c))).contains v ||
      CFSG.KC.Mat8R.rangeAllB
        (CFSG.KC.Mat8R.spanT ((elemsOf (aL c)).map (fun a => mv8 a v) ++ imgBasis (xsS c))).2 256

theorem irrB_eq : irrB = irrK := by simp only [irrB, irrK, CFSG.KC.Mat8R.all_range_spanN]

set_option maxHeartbeats 0 in
theorem q1449_xsB_true : xsB = true := by q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_cPWB_true : cPWB = true := by q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_alt0B_true : alt0B = true := by q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_cjB_true : cjB = true := by q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_x0AB_true : x0AB = true := by
  simp only [x0AB, List.all_cons, List.all_nil, Bool.and_true, aE0_eq, aE1_eq]
  q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_betaB_true : betaB = true := by q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_sigB_true : sigB = true := by
  simp only [sigB, List.all_cons, List.all_nil, Bool.and_true, aE0_eq, aE1_eq]
  q1449_tac

set_option maxHeartbeats 0 in
theorem q1449_irrB_true : irrB = true := by
  rw [irrB_eq]
  simp only [irrK, List.all_cons, List.all_nil, Bool.and_true, aE0_eq, aE1_eq]
  q1449_tac

theorem q1449_invRkB_true : invRkB = true := invRkB_of o5L0_eq o5L1_eq

theorem q1449Check_true : q1449Check = true := by
  rw [q1449Check, q1449_xsB_true, q1449_cPWB_true, q1449_alt0B_true, q1449_expB_true,
    q1449_cjB_true, q1449_x0AB_true, q1449_betaB_true, q1449_sigB_true, q1449_irrB_true,
    q1449_invRkB_true]
  rfl

end CertificateChecks.KernelH13

end
