module

public import CFSG.Quasithin.H13.L32NO3Inputs
import Certificates.Kernel.H13.O3Sub
import Certificates.Kernel.H13.O3Ov
import Certificates.Kernel.H13.O3Cen
public import CFSG.Certificates.Kernel.Mat8PSet
import CFSG.Certificates.Kernel.Mat8TSound
public import Mathlib

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert

set_option maxRecDepth 100000

theorem code64R_unpackM_mod (X : ℕ) : CFSG.KC.Mat8P.code64R (CFSG.KC.Mat8P.unpackM X) = X % 2 ^ 64 := by
  rw [CFSG.KC.Mat8P.code64R_eq, CFSG.KC.Mat8P.unpackM_eq, CFSG.KC.Mat8P.code64_unpackS]

open CFSG.KC.Mat8P in
set_option maxHeartbeats 0 in
theorem o3_cov : (omNE.all fun x => (Std.HashSet.ofList om3E).contains x ||
    (Std.HashSet.ofList om3E).contains (mul8 sG x) ||
    (Std.HashSet.ofList om3E).contains (mul8 fG x) ||
    (Std.HashSet.ofList om3E).contains (mul8 sfG x)) = true := by
  have hs : sG = unpackM (code64R sG) := by decide
  have hf : fG = unpackM (code64R fG) := by decide
  have hsf : sfG = unpackM (code64R sfG) := by decide
  have hlt : ∀ p ∈ D.om3L, p < 2 ^ 64 := fun p hp =>
    (CFSG.KC.Mat8S.nInv_elemsP (o3G.map code64R) 100000).2 p (by rw [om3L_eq]; exact hp)
  rw [omNE_eq, om3E_eq, List.all_map, hs, hf, hsf]
  simp only [Function.comp_def, mul8_unpackM, hs_contains_map _ hlt, validB_unpackM, Bool.true_and,
    code64R_unpackM_mod, CFSG.KC.Mat8T.memP_ofListP_T 16 65521]
  decide +kernel

set_option maxHeartbeats 0 in
theorem o3_basicB_true : CFSG.Quasithin.H13.O3Cert.basicB = true := by
  simp only [CFSG.Quasithin.H13.O3Cert.basicB, o3_sub_om3, o3_sub_om3F, o3_sub_omN, o3_sub_h1,
    o3_sub_h2, o3_cov, Bool.true_and, Bool.and_true]
  o3_tac

theorem o3Check_true : o3Check = true := by
  simp only [o3Check, List.all_cons, List.all_nil, o3_basicB_true, o3_h1B_true, o3_pB0, o3_pB1,
    o3_wB0, o3_wB1, o3_invB0, o3_invB1, o3_ovB0, o3_ovB1, o3_kB0, o3_kB1, o3_cenB0, o3_cenB1,
    Bool.and_true]

end CertificateChecks.KernelH13

end
