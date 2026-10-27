module

public import Certificates.Kernel.LocalComp.WittFixLev
public import Certificates.Kernel.LocalComp.WittData8165
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem k8165a0 : wcB (relT tL0 tL0) (pwp A B I wL0) (inM 1097729) (fun _ => inM 1097729)
    (fun _ _ => inM 1097729) = 36 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165a1 : wcB (relT tL1 tL1) (pwp A B I wL1) (inM 2098433) (fun _ => inM 2098433)
    (fun _ _ => inM 2098433) = 36 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165a2 : wcB (relT tL2 tL2) (pwp A B I wL2) (inM 528389) (fun _ => inM 528389)
    (fun _ _ => inM 528389) = 36 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165a3 : wcB (relT tL3 tL3) (pwp A B I wL3) (inM 264225) (fun _ => inM 264225)
    (fun _ _ => inM 264225) = 36 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165b0 : wcB (fun y => relT tL0 tL0 y && fourB y) (pwp A B I wL0) (inM 1097729)
    (fun _ => inM 1097729) (fun _ _ => inM 1097729) = 4 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165b1 : wcB (fun y => relT tL1 tL1 y && fourB y) (pwp A B I wL1) (inM 2098433)
    (fun _ => inM 2098433) (fun _ _ => inM 2098433) = 4 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165b2 : wcB (fun y => relT tL2 tL2 y && fourB y) (pwp A B I wL2) (inM 528389)
    (fun _ => inM 528389) (fun _ _ => inM 528389) = 4 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165b3 : wcB (fun y => relT tL3 tL3 y && fourB y) (pwp A B I wL3) (inM 264225)
    (fun _ => inM 264225) (fun _ _ => inM 264225) = 4 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165c : trAll trW = true := by quickRfl

theorem k8165d0 : wcB (presT 1626117 [0, 2, 12, 14, 15, 19, 20]) (pwp A B I wL2) (inM 1626117)
    (fun _ => inM 1626117) (fun _ _ => inM 1626117) = 2520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165d1 : wcB (presT 1361953 [0, 5, 11, 14, 15, 18, 20]) (pwp A B I wL3) (inM 1361953)
    (fun _ => inM 1361953) (fun _ _ => inM 1361953) = 2520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165d2 : wcB (presT 2626821 [0, 2, 8, 10, 12, 19, 21]) (pwp A B I wH2) (inM 2626821)
    (fun _ => inM 2626821) (fun _ _ => inM 2626821) = 2520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165d3 : wcB (presT 2362657 [0, 5, 8, 10, 11, 18, 21]) (pwp A B I wH3) (inM 2362657)
    (fun _ => inM 2362657) (fun _ _ => inM 2362657) = 2520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165e0 : wcB (presT 1097728 [14, 15, 20]) (pwp A B I wT0) (inM 1097728)
    (fun _ => inM 1097728) (fun _ _ => inM 1097728) = 288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165e1 : wcB (presT 2098432 [8, 10, 21]) (pwp A B I wT1) (inM 2098432)
    (fun _ => inM 2098432) (fun _ _ => inM 2098432) = 288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165e2 : wcB (presT 528388 [2, 12, 19]) (pwp A B I wT2) (inM 528388)
    (fun _ => inM 528388) (fun _ _ => inM 528388) = 288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k8165e3 : wcB (presT 264224 [5, 11, 18]) (pwp A B I wT3) (inM 264224)
    (fun _ => inM 264224) (fun _ _ => inM 264224) = 288 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
