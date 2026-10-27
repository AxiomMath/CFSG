module

public import Certificates.Kernel.LocalComp.WittLev
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CFSG.Quasithin.Asc94 CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000
theorem k7058a : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && presT 1065035 [0, 1, 3, 6, 14, 20] y &&
    presT 270387 [0, 1, 4, 5, 13, 18] y && presT 2163075 [0, 1, 7, 8, 16, 21] y &&
    presT 39939 [0, 1, 10, 11, 12, 15] y) I (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1)
    (fun _ _ => inM 655879) = 16 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7058b : wc (fun σ => ∀ p ∈ m22HexadL, σ p = p) I (fun x => Nat.beq x 0)
    (fun _ x => Nat.beq x 1) (fun _ _ x => Nat.beq x 2) = 16 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7058c1 : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && presT 1065035 [0, 1, 3, 6, 14, 20] y) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 48 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7058c2 : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && presT 270387 [0, 1, 4, 5, 13, 18] y) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 48 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7058c3 : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && presT 2163075 [0, 1, 7, 8, 16, 21] y) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 48 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k7058c4 : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
    presT 655879 [0, 1, 2, 9, 17, 19] y && presT 39939 [0, 1, 10, 11, 12, 15] y) I
    (fun x => Nat.beq x 0) (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 48 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
