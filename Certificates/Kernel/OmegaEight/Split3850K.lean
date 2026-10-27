module

public import Certificates.Data.Kernel.O8.SplitK
public import Certificates.Kernel.OmegaEight.Split3850D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Split3850

open CFSG.KC.O8Split CFSG.EvenSmallLie.OmegaEight.Stage1

theorem plus_ok :
    ySplitOK .plus 161 161 CFSG.KD.O8S.tpP CFSG.KD.O8S.taP CFSG.KD.O8S.YBP = true := by
  quickRfl

theorem minus_ok :
    ySplitOK .minus 161 161 CFSG.KD.O8S.tpM CFSG.KD.O8S.taM CFSG.KD.O8S.YBM = true := by
  quickRfl

end CertificateChecks.KernelO8.Split3850

end
