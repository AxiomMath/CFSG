module

public import Certificates.Kernel.Sporadic.OddCore.HL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt

theorem oE9_7 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 3150 450 = true := by quickRfl
theorem oE9_8 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 3600 450 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
