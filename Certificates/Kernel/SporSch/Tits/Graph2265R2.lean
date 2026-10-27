module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem kR7 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 7) (TitsGS.ST 8) (TitsGS.SC 7)
    (TitsGS.PI 7) (TitsGS.REP 8) 6 = true := by quickRfl
theorem kR8 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 8) (TitsGS.ST 9) (TitsGS.SC 8)
    (TitsGS.PI 8) (TitsGS.REP 9) 11 = true := by quickRfl
theorem kR9 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 9) (TitsGS.ST 10) (TitsGS.SC 9)
    (TitsGS.PI 9) (TitsGS.REP 10) 17 = true := by quickRfl
theorem kR10 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 10) (TitsGS.ST 11) (TitsGS.SC 10)
    (TitsGS.PI 10) (TitsGS.REP 11) 22 = true := by quickRfl
theorem kR11 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 11) (TitsGS.ST 12) (TitsGS.SC 11)
    (TitsGS.PI 11) (TitsGS.REP 12) 24 = true := by quickRfl
theorem kR12 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 12) (TitsGS.ST 13) (TitsGS.SC 12)
    (TitsGS.PI 12) (TitsGS.REP 13) 25 = true := by quickRfl
theorem kR13 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 13) (TitsGS.ST 14) (TitsGS.SC 13)
    (TitsGS.PI 13) (TitsGS.REP 14) 25 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
