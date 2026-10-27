module

public import CFSG.Quasithin.H13.L32N1447Inputs
public import CFSG.Certificates.Kernel.Mat8PSound
import Certificates.Kernel.H13.ElemsO3
import Certificates.Kernel.H13.Pow
import CFSG.Certificates.Kernel.MatNKSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.Quasithin.H13.Q1447Cert
  CFSG.KC.Mat8P

@[expose] def kbHead : Bool :=
  (s7Conj.all fun t => (Std.HashSet.ofList CFSG.Quasithin.H13.S7Cert.s7E).contains t.1 &&
      mul8 t.1 t.2.1 == one8 &&
      (Std.HashSet.ofList (elemsOf CFSG.Quasithin.H13.S7Cert.n8G)).contains t.2.2) &&
    subB (conjOf s7Conj) (elemsOf (conjOf s7Conj))

@[expose] def kbX (x : List ℕ) : Bool :=
  !(pow8 x 315 == one8) || (Std.HashSet.ofList (elemsOf (conjOf s7Conj))).contains x

theorem s7KB_split : s7KB = (kbHead && CFSG.Quasithin.H13.S7Cert.s7E.all kbX) := rfl

theorem isChain_mergeSort_eq (l : List ℕ) :
    (l.mergeSort).IsChain (· < ·) = (nodupP l = true) :=
  propext ((isChain_mergeSort_iff l).trans (nodupP_iff l).symm)

macro "q1447_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H13.Q1447Cert.s7InvB, CFSG.Quasithin.H13.Q1447Cert.g5InvB,
    CFSG.Quasithin.H13.Q1447Cert.m22InvB, CFSG.Quasithin.H13.Q1447Cert.o3InvB,
    CFSG.Quasithin.H13.Q1447Cert.g5KB, CFSG.Quasithin.H13.Q1447Cert.m22KB,
    CertificateChecks.KernelH13.kbHead, CFSG.Quasithin.H13.Q1447Cert.conjB,
    CFSG.Quasithin.H13.Q1447Cert.conjOf, CFSG.Quasithin.H13.Q1447Cert.invol8,
    CFSG.Quasithin.H13.Q1447Cert.bigImg8, CFSG.Quasithin.H13.Q1447Cert.invol12,
    CFSG.Quasithin.H13.Q1447Cert.bigImg12, CFSG.Quasithin.H13.Q1447Cert.imgBasis12,
    CFSG.Quasithin.H13.O3Cert.imgBasis, CFSG.Quasithin.H13.O3Cert.gamE,
    CFSG.Quasithin.H13.S7Cert.s7E, CFSG.Quasithin.H13.G5Cert.gSE,
    CFSG.Quasithin.H13.M22Cert.pE, CFSG.Quasithin.H13.M22Cert.e0E,
    CertificateChecks.KernelH13.omNE_eq, CertificateChecks.KernelH13.h2E_eq,
    CFSG.Quasithin.H13.Mat8Cert.subB, CFSG.Quasithin.H13.Mat8Cert.closedB,
    CFSG.KC.Mat8P.nodupB_toP, CFSG.KC.Mat8P.elemsOf_toF, CFSG.KC.MatNK.elemsOfN_toT,
    CFSG.KC.Mat8P.decide_isChain_toP, CertificateChecks.KernelH13.isChain_mergeSort_eq,
    CFSG.KC.Mat8P.hs_contains_toLR',
    CFSG.KC.Mat8P.hs_contains_toLR, CFSG.KC.Mat8P.contains_toLR, CFSG.KC.Mat8P.mul8_toF,
    CFSG.KC.Mat8P.mv8_toR, CertificateChecks.KernelH13.pow8_toF]
  decide +kernel))

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem q1447_s7InvB_true : s7InvB = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_g5InvB_true : g5InvB = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_m22InvB_true : m22InvB = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_o3InvB0 : o3InvB 0 = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_o3InvB1 : o3InvB 1 = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_g5KB_true : g5KB = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_m22KB_true : m22KB = true := by q1447_tac

set_option maxHeartbeats 0 in
theorem q1447_kbHead_true : kbHead = true := by q1447_tac

end CertificateChecks.KernelH13

end
