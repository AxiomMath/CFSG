module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.LocalComp.WittData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22InvolutionsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CFSG.ComponentClassification.WittDesign CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem k2032a : wc (fun g => ∀ x, g x = aFun x) I (fun x => Nat.beq x 12)
    (fun _ x => Nat.beq x 7) (fun _ _ x => Nat.beq x 15) = 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem k2032b : wcB (relT tA tA) dB (inM 1982480) (fun _ => inM 1982480)
    (fun _ _ => inM 1982480) = 384 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
