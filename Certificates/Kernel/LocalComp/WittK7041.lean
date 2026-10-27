module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.LocalComp.WittDataL34
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000
theorem k7041a : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1) I (fun x => Nat.beq x 0)
    (fun _ x => Nat.beq x 1) (fun _ _ _ => true) = 960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7041b : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y) I (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1)
    (fun _ _ => inM 655879) = 192 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7041c : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 && relT F1P F1P y &&
    relT F2P F2P y) I (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ _ => true) = 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7042a : wcB (fun y => Nat.beq (pt y 0) 0 && presT 655879 [0, 1, 2, 9, 17, 19] y) I
    (fun x => Nat.beq x 0) (fun _ => inM 655879) (fun _ _ => inM 655879) = 960 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
