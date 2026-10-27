module

public import Certificates.Kernel.HNDce2.Data
public import Certificates.Data.Kernel.TwistDce2.Cover

public section

namespace CFSG.KD.HNDce2

open CFSG.KC.TwDce2

theorem letters_ok : lettersOK F INVM 1408 = true := by
  decide +kernel

theorem cover_ok : coverRange F INVM 1408 RD RW 498 9 CV 0 9 = true := by
  decide +kernel

end CFSG.KD.HNDce2

end
