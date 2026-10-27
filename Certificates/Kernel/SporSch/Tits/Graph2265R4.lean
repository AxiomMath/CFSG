module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem kR24 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 24) (TitsGS.ST 25) (TitsGS.SC 24)
    (TitsGS.PI 24) (TitsGS.REP 25) 11 = true := by quickRfl
theorem kR25 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 25) (TitsGS.ST 26) (TitsGS.SC 25)
    (TitsGS.PI 25) (TitsGS.REP 26) 20 = true := by quickRfl
theorem kR26 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 26) (TitsGS.ST 27) (TitsGS.SC 26)
    (TitsGS.PI 26) (TitsGS.REP 27) 44 = true := by quickRfl
theorem kR27 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 27) (TitsGS.ST 28) (TitsGS.SC 27)
    (TitsGS.PI 27) (TitsGS.REP 28) 100 = true := by quickRfl
theorem kR28 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 28) (TitsGS.ST 29) (TitsGS.SC 28)
    (TitsGS.PI 28) (TitsGS.REP 29) 139 = true := by quickRfl
theorem kR29 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 29) (TitsGS.ST 30) (TitsGS.SC 29)
    (TitsGS.PI 29) (TitsGS.REP 30) 149 = true := by quickRfl
theorem kR30 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 30) (TitsGS.ST 31) (TitsGS.SC 30)
    (TitsGS.PI 30) (TitsGS.REP 31) 149 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
