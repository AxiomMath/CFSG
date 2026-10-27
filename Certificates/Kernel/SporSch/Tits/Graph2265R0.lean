module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem kR0 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 0) (TitsGS.ST 1) (TitsGS.SC 0)
    (TitsGS.PI 0) (TitsGS.REP 1) 1 = true := by quickRfl
theorem kR2 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 2) (TitsGS.ST 3) (TitsGS.SC 2)
    (TitsGS.PI 2) (TitsGS.REP 3) 3 = true := by quickRfl
theorem kR3 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 3) (TitsGS.ST 4) (TitsGS.SC 3)
    (TitsGS.PI 3) (TitsGS.REP 4) 4 = true := by quickRfl
theorem kR4 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 4) (TitsGS.ST 5) (TitsGS.SC 4)
    (TitsGS.PI 4) (TitsGS.REP 5) 5 = true := by quickRfl
theorem kR5 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 5) (TitsGS.ST 6) (TitsGS.SC 5)
    (TitsGS.PI 5) (TitsGS.REP 6) 5 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
