module

public import Certificates.Kernel.HNDce2.Data
public import Certificates.Data.Kernel.TwistDce2.Cover

public section

namespace CFSG.KD.HNDce2

open CFSG.KC.TwDce2

theorem stab_ok : stabRange F INVM 1408 RD RW 498 CG CW CB CS CT
    [177408000, 126000, 1440, 5040, 80640, 500, 240, 640, 30720] 0 9 = true := by
  decide +kernel

end CFSG.KD.HNDce2

end
