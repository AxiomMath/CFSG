module

public import Certificates.Kernel.IdxFour.E0Data
public import Certificates.Kernel.IdxFour.M0Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4M

open CFSG.KC.IF4C CFSG.KC.IF4M

theorem cf17600m0 :
    m0OK CFSG.KD.IF4E.SP CFSG.KD.IF4E.T CFSG.KD.IF4E.O CFSG.KD.IF4E.PS CFSG.KD.IF4E.B MT Q QI
      AW CJ CS NG = true := by
  decide +kernel

end CFSG.KD.IF4M

end
