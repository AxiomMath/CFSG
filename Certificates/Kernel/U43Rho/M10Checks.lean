module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.U43Rho.O6Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Rho

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

theorem kPhi57 : inPK (pc (CU43T 1) (pc (TK 5) (pc (CU43T 1) (TKI 7)))) = true := by quickRfl
theorem kPhi75 : inPK (pc (CU43T 1) (pc (TK 7) (pc (CU43T 1) (TKI 5)))) = true := by quickRfl
theorem kO6b : bindListK 820 10 (O6 0) order6W.toList = true := by quickRfl
theorem kO6i : invEqK 820 10 (mask 10) (820 * 10) (O6 0) (O6 1) = true := by quickRfl
theorem kO6p : inPK (O6 0) = true := by quickRfl
theorem kO6c : Nat.beq (pc (O6 0) (CU43T 10)) (pc (CU43T 10) (O6 0)) = true := by quickRfl
theorem kO6e : Nat.beq (ppow (O6 0) 6) (pidn 820 10) = true := by quickRfl
theorem kO6m2 : bIf(Nat.beq (pg 10 (mask 10) (ppow (O6 0) 2) 0) 0, false, true) = true := by
  quickRfl
theorem kO6m3 : bIf(Nat.beq (pg 10 (mask 10) (ppow (O6 0) 3) 0) 0, false, true) = true := by
  quickRfl

end CertificateChecks.KernelU43Rho
