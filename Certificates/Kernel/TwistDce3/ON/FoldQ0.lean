module

public import Certificates.Kernel.TwistDce3.ON.Data
public import Certificates.Data.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce3Q

theorem foldq0 :
    foldIs (isOneQ4 PB F BS) INVM NT PSF PSB RD RW RA WD RJ 0 1670 1 131 = true := by
  quickRfl

end CFSG.KD.ONDce3

end
