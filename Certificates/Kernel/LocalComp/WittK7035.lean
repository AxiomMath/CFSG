module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.LocalComp.WittDataL34
public import Certificates.Data.Kernel.WittConj
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000
theorem k7037 : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && !memN bPk y) I (fun x => Nat.beq x 0)
    (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7035a : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    !presT 655879 [0, 1, 2, 9, 17, 19] y && invT I y && !conjAny bPk [t1P] y) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ _ => true) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7035b : wcB (fun y => Nat.beq (pt y 0) 0 && !Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && invT I y && !conjAny cbP repP y) I
    (fun x => Nat.beq x 0) (fun _ x => inM 655879 x && !Nat.beq x 1) (fun _ _ => inM 655879) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
