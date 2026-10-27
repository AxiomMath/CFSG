module

public import CFSG.Certificates.Kernel.E6Syl3Glue
public import Certificates.Kernel.E6Syl3.Checks

public section

namespace CFSG.KD.E6Syl3

open CFSG.KC.E6Syl3

theorem e6Order3Kinds :
    CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3Kinds :=
  e6Order3Kinds_of_checks (gw := gw) (W := kw) (by rw [ch214105_tups]; exact ch214105_q)
    (by rw [ch214105_tups]; exact ch214105_kinds)

end CFSG.KD.E6Syl3
