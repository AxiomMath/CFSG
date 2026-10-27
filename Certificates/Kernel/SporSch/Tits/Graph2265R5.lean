module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem kR32 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 32) (TitsGS.ST 33) (TitsGS.SC 32)
    (TitsGS.PI 32) (TitsGS.REP 33) 14 = true := by quickRfl
theorem kR33 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 33) (TitsGS.ST 34) (TitsGS.SC 33)
    (TitsGS.PI 33) (TitsGS.REP 34) 26 = true := by quickRfl
theorem kR34 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 34) (TitsGS.ST 35) (TitsGS.SC 34)
    (TitsGS.PI 34) (TitsGS.REP 35) 80 = true := by quickRfl
theorem kR35 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 35) (TitsGS.ST 36) (TitsGS.SC 35)
    (TitsGS.PI 35) (TitsGS.REP 36) 336 = true := by quickRfl
theorem kR36 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 36) (TitsGS.ST 37) (TitsGS.SC 36)
    (TitsGS.PI 36) (TitsGS.REP 37) 470 = true := by quickRfl
theorem kR37 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 37) (TitsGS.ST 38) (TitsGS.SC 37)
    (TitsGS.PI 37) (TitsGS.REP 38) 477 = true := by quickRfl
theorem kR38 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 38) (TitsGS.ST 39) (TitsGS.SC 38)
    (TitsGS.PI 38) (TitsGS.REP 39) 477 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
