module

public import Certificates.Kernel.McLNine.Enum
public import Certificates.Data.Kernel.McLNine.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLNine

open CFSG.KS.McLNine CFSG.Sporadic.SmallOddCore

theorem chk : mcl9K McLCT.F MUE.G MUE.T MUE.PL MUE.POS MUE.SRT MUE.SRI MUE.cnt MUE.CW
    mclIndexNineUWords mclIndexNineX mclIndexNineY mclIndexNinePoint mclIndexNineOrbitWords
    mclIndexNineOrbitPoints = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLNine

end
