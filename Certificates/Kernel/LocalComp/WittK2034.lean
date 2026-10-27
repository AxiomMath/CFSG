module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.LocalComp.WittData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCasesInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CFSG.ComponentClassification.WittDesign CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem k2034o1 : wcB (presT 3179043 [0, 1, 5, 9, 15, 20, 21]) dO1 (inM 3179043)
    (fun _ => inM 3179043) (fun _ _ => inM 3179043) = 2520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034o2 : wcB (presT 475404 [2, 3, 8, 14, 16, 17, 18]) dO2 (inM 475404)
    (fun _ => inM 475404) (fun _ _ => inM 475404) = 168 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034o3 : wcB (presT 539840 [6, 7, 10, 11, 12, 13, 19]) dO3 (inM 539840)
    (fun _ => inM 539840) (fun _ _ => inM 539840) = 2520 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034p : wc InP2 I (inM 3) (fun _ => inM 3) (fun _ _ => inM 655879) = 128 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034p0 : wc (fun f => InP2 f ∧ f 0 = 0) I (inM 3) (fun _ => inM 3)
    (fun _ _ => inM 655879) = 64 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034p2 : wc (fun f => InP2 f ∧ f 2 = 2) I (inM 3) (fun _ => inM 3)
    (fun _ _ => inM 655879) = 32 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034p3 : wc (fun f => InP2 f ∧ f 3 = 3) I (inM 3) (fun _ => inM 3)
    (fun _ _ => inM 655879) = 8 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2034x : wcB (presT 3 [0, 1]) I (inM 3) (fun _ => inM 3) (fun _ _ _ => true) = 1920 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
