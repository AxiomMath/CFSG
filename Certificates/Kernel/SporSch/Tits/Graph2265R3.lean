module

public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem kR15 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 15) (TitsGS.ST 16) (TitsGS.SC 15)
    (TitsGS.PI 15) (TitsGS.REP 16) 9 = true := by quickRfl
theorem kR16 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 16) (TitsGS.ST 17) (TitsGS.SC 16)
    (TitsGS.PI 16) (TitsGS.REP 17) 16 = true := by quickRfl
theorem kR17 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 17) (TitsGS.ST 18) (TitsGS.SC 17)
    (TitsGS.PI 17) (TitsGS.REP 18) 28 = true := by quickRfl
theorem kR18 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 18) (TitsGS.ST 19) (TitsGS.SC 18)
    (TitsGS.PI 18) (TitsGS.REP 19) 47 = true := by quickRfl
theorem kR19 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 19) (TitsGS.ST 20) (TitsGS.SC 19)
    (TitsGS.PI 19) (TitsGS.REP 20) 74 = true := by quickRfl
theorem kR20 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 20) (TitsGS.ST 21) (TitsGS.SC 20)
    (TitsGS.PI 20) (TitsGS.REP 21) 85 = true := by quickRfl
theorem kR21 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 21) (TitsGS.ST 22) (TitsGS.SC 21)
    (TitsGS.PI 21) (TitsGS.REP 22) 86 = true := by quickRfl
theorem kR22 : refK 1755 10 1756 11 TitsGN.NB (TitsGS.ST 22) (TitsGS.ST 23) (TitsGS.SC 22)
    (TitsGS.PI 22) (TitsGS.REP 23) 86 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsGraph

end
