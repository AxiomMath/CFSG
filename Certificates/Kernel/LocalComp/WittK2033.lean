module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.LocalComp.WittData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CFSG.ComponentClassification.WittDesign CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem k2033w : wc (fun g => ∀ x, g x = ofTable wTab x) I (fun x => Nat.beq x 5)
    (fun _ x => Nat.beq x 0) (fun _ _ x => Nat.beq x 18) = 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2033c : wc (fun g => ∀ x, g x = ofTable cTab x) I (fun x => Nat.beq x 3)
    (fun _ x => Nat.beq x 0) (fun _ _ x => Nat.beq x 18) = 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2033y : wc (fun g => ∀ x, g x = ofTable yTab x) I (fun x => Nat.beq x 15)
    (fun _ x => Nat.beq x 21) (fun _ _ x => Nat.beq x 14) = 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2033nz : wcB (relAny tZ tZs) dZ (fun _ => true)
    (fun x0 x1 => decide (∃ j : Fin 11, x1 = pt (tZs.getD j.val 0) x0))
    (fun x0 x1 x2 => decide (∃ j : Fin 11, x1 = pt (tZs.getD j.val 0) x0 ∧
      x2 = pt (tZs.getD j.val 0) x1)) = 55 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2033nw : wcB (relAny tW tWs) dW (inM 4352) (fun _ => inM 4352) (fun _ _ _ => true) = 20 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2033ny : wcB (relAny tY tYs) dY (fun x => Nat.beq x 4) (fun _ _ => true)
    (fun _ x1 x2 => decide (∃ j : Fin 7, x2 = pt (tYs.getD j.val 0) x1)) = 21 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
