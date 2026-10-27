module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Data.Kernel.WittConj
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000
theorem k7103 : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && invT I y &&
    !(presT 655879 [0, 1, 2, 9, 17, 19] y && presT 1065035 [0, 1, 3, 6, 14, 20] y &&
      presT 270387 [0, 1, 4, 5, 13, 18] y && presT 2163075 [0, 1, 7, 8, 16, 21] y &&
      presT 39939 [0, 1, 10, 11, 12, 15] y) &&
    !(Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 && Nat.beq (pt y 2) 2 && Nat.beq (pt y 9) 9 &&
      Nat.beq (pt y 17) 17 && Nat.beq (pt y 19) 19)) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

set_option maxRecDepth 100000
end CertificateChecks.KernelLC.Witt

end
