module

public import CFSG.Quasithin.H13.L32NO3Inputs
public import Certificates.Kernel.H13.ElemsO3
public import Certificates.Kernel.H13.Pow
public import Certificates.Kernel.H13.PowP
public import CFSG.Certificates.Kernel.Mat8SSound
public import CFSG.Certificates.Kernel.Mat8CSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.Quasithin.H13.G5Cert
  CFSG.Quasithin.H13.O3Cert CFSG.KC.Mat8P

theorem pow8F_unpackM (X k : ℕ) : pow8F (unpackM X) k = unpackM (powP X k) := by
  rw [← pow8_toF, pow8_unpackM]

theorem beq_one_powP (X k : ℕ) : (unpackM (powP X k) == one8) = (powP X k == oneP) := by
  rw [← pow8_unpackM, pow8_beq_one]

macro "o3_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H13.O3Cert.basicB, h1B, CFSG.Quasithin.H13.O3Cert.pB,
    CFSG.Quasithin.H13.O3Cert.wB, invB, CFSG.Quasithin.H13.O3Cert.ovB, kB, cenB, gamE,
    CFSG.Quasithin.H13.O3Cert.pE, wE, cxs, CFSG.Quasithin.H13.O3Cert.mE, oME,
    CFSG.Quasithin.H13.S7Cert.oddOf, om3E_eq,
    om3FE_eq, omNE_eq, h1E_eq, h2E_eq, subB, nodupB_toP, elemsOf_toF, smallImgB,
    imgBasis, fullImgB, decide_isChain_toP, b5N, quadN, List.any_map, Function.comp_def,
    hs_contains_toLR', hs_contains_toLR, contains_toLR, hsN_contains_toP', hsN_contains_toP,
    mul8_toF, mv8_toR, CertificateChecks.KernelH13.pow8_toF]
  try simp only [CFSG.KC.Mat8S.closedB_elemsF, CFSG.KC.Mat8S.nodupP_elemsF_if,
    CFSG.KC.Mat8S.all_validB_elemsF, CFSG.KC.Mat8S.memLR_elemsF_one,
    CFSG.KC.Mat8S.all_memLR_elemsF]
  try simp only [closedB, hs_contains_toLR', hs_contains_toLR, contains_toLR, mul8_toF]
  try simp only [CFSG.KC.Mat8S.all_elemsF, CFSG.KC.Mat8S.any_elemsF, List.all_map, List.any_map,
    List.filter_map, Function.comp_def, CFSG.KC.Mat8S.mul8F_unpackM, pow8F_unpackM,
    CFSG.KC.Mat8S.beq_one_mulP, CFSG.KC.Mat8S.beq_mulP_mulP, beq_one_powP]
  try simp only [CFSG.KC.Mat8C.closedP_elemsP 16 65521, CFSG.KC.Mat8C.lt_length_elemsF 8 251]
  try simp only [CFSG.KC.Mat8C.elemsP_eq_C 16 65521]
  decide +kernel))

macro "o3_sub_tac" : tactic => `(tactic| (
  simp only [subB, nodupB_toP, elemsOf_toF, contains_toLR]
  simp only [CFSG.KC.Mat8S.closedB_elemsF, CFSG.KC.Mat8S.nodupP_elemsF_if,
    CFSG.KC.Mat8S.all_validB_elemsF, CFSG.KC.Mat8S.memLR_elemsF_one]
  simp only [CFSG.KC.Mat8C.closedP_elemsP 16 65521]
  simp only [CFSG.KC.Mat8C.elemsP_eq_C 16 65521]
  decide +kernel))

end CertificateChecks.KernelH13

end
