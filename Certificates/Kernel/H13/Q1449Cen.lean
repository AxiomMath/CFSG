module

public import CFSG.Quasithin.H13.L32N1449Inputs
public import Certificates.Kernel.H13.ElemsO3
public import Certificates.Kernel.H13.OrdP
public import Certificates.Kernel.H13.DataQ1449
import Certificates.Kernel.H13.DataCen

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.Quasithin.H13.Q1449Cert
  CFSG.KC.Mat8P

set_option maxRecDepth 100000

private theorem q1449_filter_comm (L : List ℕ) (p : ℕ) (CP : List ℕ)
    (h : (L.filter fun x => mulP x p == mulP p x) == CP) :
    (L.map unpackM).filter (fun x => mul8 x (unpackM p) == mul8 (unpackM p) x) =
      CP.map unpackM := by
  rw [← eq_of_beq h, List.filter_map]
  refine congrArg (List.map unpackM) (List.filter_congr fun x _ => ?_)
  rw [Function.comp_apply, mul8_unpackM, mul8_unpackM, unpackM_beq (mulP_lt _ _) (mulP_lt _ _)]

private theorem q1449_filter_pow (CP AP : List ℕ)
    (h : (CP.filter fun x => powP x 15 == oneP) == AP) :
    (CP.map unpackM).filter (fun x => pow8 x 15 == one8) = AP.map unpackM := by
  rw [← eq_of_beq h, List.filter_map]
  refine congrArg (List.map unpackM) (List.filter_congr fun x _ => ?_)
  rw [Function.comp_apply, pow8_beq_one]

private theorem q1449_elemsOf (AP EP : List ℕ) (hv : (AP.map unpackM).all validB = true)
    (hc : ((AP.map unpackM).map code64R == AP) = true) (he : (elemsP AP == EP) = true) :
    elemsOf (AP.map unpackM) = EP.map unpackM := by
  rw [elemsOf_eqP _ hv, eq_of_beq hc, eq_of_beq he]

private theorem xs0 : xsS 0 = unpackM 10946295793368367362 := by decide +kernel

private theorem xs1 : xsS 1 = unpackM 8617934786034467331 := by decide +kernel

private theorem gam0 : gamE 0 = D.h2L.map unpackM := by rw [gamE, if_pos rfl, h2E_eq]

private theorem gam1 : gamE 1 = D.omNL.map unpackM := by rw [gamE, if_neg Nat.one_ne_zero, omNE_eq]

set_option maxHeartbeats 0 in
private theorem cen0 : (gamE 0).filter (fun x => mul8 x (xsS 0) == mul8 (xsS 0) x) =
    DC.cL0_3.map unpackM := by
  rw [gam0, xs0]
  exact q1449_filter_comm D.h2L _ DC.cL0_3 (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem cen1 : (gamE 1).filter (fun x => mul8 x (xsS 1) == mul8 (xsS 1) x) =
    DC.cL1_3.map unpackM := by
  rw [gam1, xs1]
  exact q1449_filter_comm D.omNL _ DC.cL1_3 (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem aL0 : aL 0 = DC.aL0_3.map unpackM := by
  rw [aL, cen0, q1449_filter_pow DC.cL0_3 DC.aL0_3 (by decide +kernel)]

set_option maxHeartbeats 0 in
private theorem aL1 : aL 1 = DC.aL1_3.map unpackM := by
  rw [aL, cen1, q1449_filter_pow DC.cL1_3 DC.aL1_3 (by decide +kernel)]

set_option maxHeartbeats 0 in
theorem aE0_eq : elemsOf (aL 0) = D.aE0.map unpackM := by
  rw [aL0]
  exact q1449_elemsOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
theorem aE1_eq : elemsOf (aL 1) = D.aE1.map unpackM := by
  rw [aL1]
  exact q1449_elemsOf _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem exp0 : ((gamE 0).filter fun x => mul8 x (xsS 0) == mul8 (xsS 0) x).all
    (fun x => pow8 x 240 == one8) = true := by
  rw [cen0]
  exact all_pow8_of_ord8B 240 _ (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem exp1 : ((gamE 1).filter fun x => mul8 x (xsS 1) == mul8 (xsS 1) x).all
    (fun x => pow8 x 240 == one8) = true := by
  rw [cen1]
  exact all_pow8_of_ord8B 240 _ (by decide +kernel)

theorem q1449_expB_true : expB = true := by
  simp only [expB, List.all_cons, List.all_nil, Bool.and_true, exp0, exp1]

private theorem q1449_filter_o5 (L OP : List ℕ)
    (h : (L.filter fun A => powP A 5 == oneP && unpackM A != one8) == OP) :
    (L.map unpackM).filter (fun a => pow8 a 5 == one8 && a != one8) = OP.map unpackM := by
  rw [← eq_of_beq h, List.filter_map]
  refine congrArg (List.map unpackM) (List.filter_congr fun x _ => ?_)
  rw [Function.comp_apply, pow8_beq_one]

set_option maxHeartbeats 0 in
theorem o5L0_eq : o5L 0 = D.o5L0.map unpackM := by
  rw [o5L, gam0]
  exact q1449_filter_o5 _ _ (by decide +kernel)

set_option maxHeartbeats 0 in
theorem o5L1_eq : o5L 1 = D.o5L1.map unpackM := by
  rw [o5L, gam1]
  exact q1449_filter_o5 _ _ (by decide +kernel)

end CertificateChecks.KernelH13

end
