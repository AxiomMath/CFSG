module

public import Certificates.Kernel.LocalComp.WittLev
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizerInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CFSG.ComponentClassification.WittDesign CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem k2030a : wc (fun g => ∀ x ∈ hexad0, g x = x) I (fun x => Nat.beq x 0)
    (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 16 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2030b : wc (fun g => (∀ x ∈ hexad0, g x = x) ∧ ∀ x, g (g x) = x) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 16 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2030c : wc (fun g => (∀ x ∈ hexad0, g x = x) ∧ g 3 = 3) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2030d : wcB (fun y => presT 655879 [0, 1, 2, 9, 17, 19] y &&
    presT 1085496 [3, 4, 5, 12, 15, 20] y) I (inM 655879) (fun _ => inM 655879)
    (fun _ _ => inM 655879) = 360 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2030e : wcB (fun y => presT 655879 [0, 1, 2, 9, 17, 19] y &&
    presT 1065035 [0, 1, 3, 6, 14, 20] y) I (inM 3) (fun _ => inM 3)
    (fun _ _ => inM 655879) = 96 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
