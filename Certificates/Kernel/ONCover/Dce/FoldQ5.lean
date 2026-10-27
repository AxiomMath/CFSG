module

public import Certificates.Kernel.ONCover.Dce.Data
public import Certificates.Data.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3Q

theorem foldq5 :
    foldIs (isOneQ4 PB F BS) INVM NT PSF PSB RD RW RA WD RJ 9331 1154 775 775 = true := by
  quickRfl

end CFSG.KD.ONCoverDce3

end
