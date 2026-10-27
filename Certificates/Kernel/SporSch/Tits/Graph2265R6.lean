module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem kR40 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 40) (TitsGS.ST 41) (TitsGS.SC 40)
    (TitsGS.PI 40) (TitsGS.REP 41) 17 = true := by quickRfl
theorem kR41 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 41) (TitsGS.ST 42) (TitsGS.SC 41)
    (TitsGS.PI 41) (TitsGS.REP 42) 36 = true := by quickRfl
theorem kR42 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 42) (TitsGS.ST 43) (TitsGS.SC 42)
    (TitsGS.PI 42) (TitsGS.REP 43) 167 = true := by quickRfl
theorem kR43 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 43) (TitsGS.ST 44) (TitsGS.SC 43)
    (TitsGS.PI 43) (TitsGS.REP 44) 1404 = true := by quickRfl
theorem kR44 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 44) (TitsGS.ST 45) (TitsGS.SC 44)
    (TitsGS.PI 44) (TitsGS.REP 45) 1748 = true := by quickRfl
theorem kR45 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 45) (TitsGS.ST 46) (TitsGS.SC 45)
    (TitsGS.PI 45) (TitsGS.REP 46) 1755 = true := by quickRfl
theorem kR46 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 46) (TitsGS.ST 47) (TitsGS.SC 46)
    (TitsGS.PI 46) (TitsGS.REP 47) 1755 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
