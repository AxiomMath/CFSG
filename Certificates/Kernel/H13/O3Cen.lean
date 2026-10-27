module

public import Certificates.Kernel.H13.O3Tac
import Certificates.Kernel.H13.DataCen

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.Quasithin.H13.G5Cert
  CFSG.Quasithin.H13.O3Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem o3_h1B_true : h1B = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_pB0 : CFSG.Quasithin.H13.O3Cert.pB 0 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_pB1 : CFSG.Quasithin.H13.O3Cert.pB 1 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_wB0 : CFSG.Quasithin.H13.O3Cert.wB 0 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_wB1 : CFSG.Quasithin.H13.O3Cert.wB 1 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_invB0 : invB 0 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_invB1 : invB 1 = true := by o3_tac

private def cenR (C Ag : List (List ℕ)) (i : List ℕ) : Bool :=
  let A := elemsOf Ag
  subB Ag A && A.length == 60 &&
    C.all fun x => x == one8 || x == i || !(pow8 x 16 == one8) ||
      Ag.any fun a =>
        let cm := mul8 (mul8 (pow8 x 15) (pow8 a 14)) (mul8 x a)
        pow8 cm 15 == one8 && !(cm == one8)

private def cenI (L : List (List ℕ)) (i : List ℕ) : Bool :=
  let C := L.filter fun x => mul8 x i == mul8 i x
  cenR C (C.filter fun x => pow8 x 15 == one8) i

private theorem cenB_eq (c : ℕ) : cenB c = (wE c).all fun i =>
    (Std.HashSet.ofList om3E : Std.HashSet (List ℕ)).contains i || cenI (gamE c) i := rfl

private theorem cenI_eq (L : List (List ℕ)) (i : List ℕ) (C Ag : List (List ℕ))
    (hC : L.filter (fun x => mul8 x i == mul8 i x) = C)
    (hA : C.filter (fun x => pow8 x 15 == one8) = Ag) : cenI L i = cenR C Ag i := by
  rw [cenI, hC, hA]

private theorem filter_comm_unpackM (L : List ℕ) (p : ℕ) (CP : List ℕ)
    (h : (L.filter fun x => mulP x p == mulP p x) == CP) :
    (L.map unpackM).filter (fun x => mul8 x (unpackM p) == mul8 (unpackM p) x) =
      CP.map unpackM := by
  rw [← eq_of_beq h, List.filter_map]
  congr 1
  refine List.filter_congr fun x _ => ?_
  rw [Function.comp_apply, mul8_unpackM, mul8_unpackM, unpackM_beq (mulP_lt _ _) (mulP_lt _ _)]

private theorem filter_pow_unpackM (CP AP : List ℕ)
    (h : (CP.filter fun x => powP x 15 == oneP) == AP) :
    (CP.map unpackM).filter (fun x => pow8 x 15 == one8) = AP.map unpackM := by
  rw [← eq_of_beq h, List.filter_map]
  congr 1
  refine List.filter_congr fun x _ => ?_
  rw [Function.comp_apply, pow8_beq_one]

private theorem gamE_zero : gamE 0 = D.h2L.map unpackM := by rw [gamE, if_pos rfl, h2E_eq]

private theorem gamE_one : gamE 1 = D.omNL.map unpackM := by
  rw [gamE, if_neg Nat.one_ne_zero, omNE_eq]

macro "o3_cen_tac" gl:ident L:term:max p:term:max cl:ident al:ident : tactic => `(tactic| (
  rw [$gl:ident, cenI_eq _ _ _ _ (filter_comm_unpackM $L $p $cl (by decide +kernel))
    (filter_pow_unpackM $cl $al (by decide +kernel))]
  simp only [cenR]
  o3_tac))

set_option maxHeartbeats 0 in
private theorem o3_wE0 : wE 0 = DC.wL0.map unpackM := eq_of_beq (by o3_tac)

set_option maxHeartbeats 0 in
private theorem o3_wE1 : wE 1 = DC.wL1.map unpackM := eq_of_beq (by o3_tac)

set_option maxHeartbeats 0 in
private theorem o3_cen0_0 : cenI (gamE 0) (unpackM 16679624893928243029) = true := by
  o3_cen_tac gamE_zero D.h2L 16679624893928243029 DC.cL0_0 DC.aL0_0

set_option maxHeartbeats 0 in
private theorem o3_cen0_1 : cenI (gamE 0) (unpackM 8618094080076666475) = true := by
  o3_cen_tac gamE_zero D.h2L 8618094080076666475 DC.cL0_1 DC.aL0_1

set_option maxHeartbeats 0 in
private theorem o3_cen0_2 : cenI (gamE 0) (unpackM 507075620262692940) = true := by
  o3_cen_tac gamE_zero D.h2L 507075620262692940 DC.cL0_2 DC.aL0_2

set_option maxHeartbeats 0 in
private theorem o3_cen0_3 : cenI (gamE 0) (unpackM 10946295793368367362) = true := by
  o3_cen_tac gamE_zero D.h2L 10946295793368367362 DC.cL0_3 DC.aL0_3

set_option maxHeartbeats 0 in
private theorem o3_cen1_0 : cenI (gamE 1) (unpackM 18398717018118151021) = true := by
  o3_cen_tac gamE_one D.omNL 18398717018118151021 DC.cL1_0 DC.aL1_0

set_option maxHeartbeats 0 in
private theorem o3_cen1_1 : cenI (gamE 1) (unpackM 13537184786050053466) = true := by
  o3_cen_tac gamE_one D.omNL 13537184786050053466 DC.cL1_1 DC.aL1_1

set_option maxHeartbeats 0 in
private theorem o3_cen1_2 : cenI (gamE 1) (unpackM 3679757763075498096) = true := by
  o3_cen_tac gamE_one D.omNL 3679757763075498096 DC.cL1_2 DC.aL1_2

set_option maxHeartbeats 0 in
private theorem o3_cen1_3 : cenI (gamE 1) (unpackM 8617934786034467331) = true := by
  o3_cen_tac gamE_one D.omNL 8617934786034467331 DC.cL1_3 DC.aL1_3

set_option maxHeartbeats 0 in
theorem o3_cenB0 : cenB 0 = true := by
  rw [cenB_eq, o3_wE0]
  simp only [DC.wL0, List.map_cons, List.map_nil, List.all_cons, List.all_nil, o3_cen0_0,
    o3_cen0_1, o3_cen0_2, o3_cen0_3, Bool.or_true, Bool.true_and, Bool.and_true]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_cenB1 : cenB 1 = true := by
  rw [cenB_eq, o3_wE1]
  simp only [DC.wL1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, o3_cen1_0,
    o3_cen1_1, o3_cen1_2, o3_cen1_3, Bool.or_true, Bool.true_and, Bool.and_true]
  o3_tac

end CertificateChecks.KernelH13

end
