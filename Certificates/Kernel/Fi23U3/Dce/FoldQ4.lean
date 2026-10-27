module

public import Certificates.Kernel.Fi23U3.Dce.Data
public import Certificates.Data.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce3Q

theorem foldq4 :
    foldIs (isOneQ4 PB F BS) INVM NT PSF PSB RD RW RA WD RJ 18945 5538 2730 2735 = true := by
  quickRfl

end CFSG.KD.Fi23Dce3

end
