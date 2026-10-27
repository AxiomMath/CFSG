module

public import Certificates.Kernel.HNDce2.Data
public import Certificates.Data.Kernel.TwistDce2.Defs

public section

namespace CFSG.KD.HNDce2

open CFSG.KC.TwDce2

theorem fold1 : foldRange F INVM BS NB RD RW RA WD RJ 250 248 10 = 10 := by
  decide +kernel

end CFSG.KD.HNDce2

end
