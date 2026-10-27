module

public import CFSG.Certificates.Kernel.E6Syl3PSound
public import Certificates.Kernel.E6Syl3.Checks
public import Certificates.Kernel.E6Syl3.ChecksP

public section

namespace CFSG.KD.E6Syl3

open CFSG.KC.E6Syl3

theorem e6Order3Pairs :
    CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3Pairs :=
  e6Order3Pairs_of_checks (gw := gw) (wd := wd) (lt := lt) (kw := kw) (bw := bw) (o3 := o3)
    (by rw [ch214105_tups]; exact ch214105_q) (by rw [ch214105_tups]; exact ch214107_wd)
    (by rw [ch214105_tups]; exact ch214107_lt) (by rw [ch214105_tups]; exact ch214105_kinds)
    ch214107_o3 (by rw [ch214105_tups]; exact ch214107_pairs)

end CFSG.KD.E6Syl3
