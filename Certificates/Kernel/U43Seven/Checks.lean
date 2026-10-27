module

public import Certificates.Kernel.CU43Aut.Cls
public import Certificates.Kernel.U43Seven.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43SevenInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Seven

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.HSStd.U43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def ord7K (r : Nat) : Bool :=
  bAnd(Nat.beq (pc r (pc r (pc r (pc r (pc r (pc r r)))))) (pidn 820 10),
    bIf(Nat.beq r (pidn 820 10), false, true))

theorem w7Bind : bindListK 820 10 (W7P 0) w7Arr.toList = true := by quickRfl

theorem w7Ok : bAnd(cK (W7P 0), bAnd(inPK (W7P 0), ord7K (W7P 0))) = true := by quickRfl

theorem w7Conj : bAnd(cK (G0P 0), bAnd(inPK (G0P 0),
    Nat.beq (pc (G0P 0) (W7P 0)) (pc (WPP 0) (G0P 0)))) = true := by quickRfl

theorem kUW : ubOK (WPP 0) OWP 7 = true := by quickRfl

theorem kLW : lbOK (WPP 0) GWP TWP 1 1 7 = true := by quickRfl

end CertificateChecks.KernelU43Seven

end
