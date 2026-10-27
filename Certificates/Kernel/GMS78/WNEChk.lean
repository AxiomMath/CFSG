module

public import Certificates.Data.Kernel.GMS78RuNE
public import Certificates.Data.GMS78RuNECheck
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelGMS78.NE

open CFSG.KC.GMS CFSG.ComponentClassification.GMS78.RuNE

theorem kact_ok :
    kAct neMulTab neConjTab neConjLetters neActWords neOrbitWords neOrbitWit = true := by
  quickRfl

theorem kw0_ok : kW0 neConjTab neConjLetters [5, 0, 2, 6] = true := by quickRfl

end CertificateChecks.KernelGMS78.NE

end
