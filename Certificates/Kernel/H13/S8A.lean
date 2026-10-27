module

public import CFSG.Quasithin.H13.L32NS8Inputs
import Certificates.Kernel.H13.ElemsS8
import CFSG.Certificates.Kernel.Mat8PSet
public import Mathlib

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem s8_basicB_true : s8BasicB = true := by
  rw [s8BasicB, s8E_eq, unpack_code64R_map s8G (by decide), subB, all_validB_map,
    all_validB_map, closedB_map _ _ s8L_lt, nodupB_map _ s8L_lt, contains_map _ s8L_lt,
    List.length_map]
  decide +kernel

macro "s8_tac" : tactic => `(tactic| (
  simp only [orbB, zB, nB, CFSG.Quasithin.H13.S8Cert.wB, fB, stE, invSt, eSpan8, nodupN,
    s8E_eq, subB, closedB, nodupB_toP, elemsOf_toF, decide_isChain_toP, List.any_map,
    Function.comp_def, hs_contains_toLR', hs_contains_toLR, contains_toLR, hsN_contains_toP',
    hsN_contains_toP, mul8_toF, mv8_toR]
  decide +kernel))

set_option maxHeartbeats 0 in
theorem s8_orbB_true : orbB = true := by s8_tac

set_option maxHeartbeats 0 in
theorem s8_zB_true : zB = true := by s8_tac

set_option maxHeartbeats 0 in
theorem s8_nB_true : nB = true := by s8_tac

set_option maxHeartbeats 0 in
theorem s8_wB_true : CFSG.Quasithin.H13.S8Cert.wB = true := by s8_tac

set_option maxHeartbeats 0 in
theorem s8_fB_true : fB = true := by s8_tac

end CertificateChecks.KernelH13

end
