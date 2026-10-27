module

public import Certificates.Kernel.Fi22Ax.Defs
public import Certificates.Data.Kernel.Spor.Co2Shape
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Ax

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CertificateChecks.KernelSpor
open CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem cnL : allN 10 (fun k => bAnd(cn (Fi22ExtT.L (11 + k)), cn (Fi22E2067.EI (11 + k)))) =
    true := by quickRfl

theorem btOK : allN 10 (fun i => Nat.beq (BT i) (axWordK axBasWords[i]!)) = true := by quickRfl

theorem sqOK : allN 10 (fun i => Nat.beq (pc (BT i) (BT i)) (pidn 3510 12)) = true := by quickRfl

theorem commOK : allN 10 (fun i => allN i fun j => Nat.beq (pc (BT i) (BT j)) (pc (BT j) (BT i))) =
    true := by quickRfl

theorem cj0 : axConjSl 0 = true := by quickRfl
theorem cj1 : axConjSl 1 = true := by quickRfl
theorem cj2 : axConjSl 2 = true := by quickRfl
theorem cj3 : axConjSl 3 = true := by quickRfl
theorem cj4 : axConjSl 4 = true := by quickRfl
theorem cj5 : axConjSl 5 = true := by quickRfl
theorem cj6 : axConjSl 6 = true := by quickRfl
theorem cj7 : axConjSl 7 = true := by quickRfl
theorem cj8 : axConjSl 8 = true := by quickRfl
theorem cj9 : axConjSl 9 = true := by quickRfl

theorem distOK : distinctL 3510 ((List.range 1024).map axImgK) 0 = true := by quickRfl

end CertificateChecks.KernelFi22Ax

end
