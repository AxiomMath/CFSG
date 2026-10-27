module

public import Certificates.Kernel.ONCover.Dce.Data
public import Certificates.Data.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3Q

theorem foldq3 :
    foldIs (isOneQ4 PB F BS) INVM NT PSF PSB RD RW RA WD RJ 4565 1887 560 775 = true := by
  quickRfl

end CFSG.KD.ONCoverDce3

end
