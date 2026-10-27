module

public import CFSG.Certificates.Kernel.E6O2Glue
public import Certificates.Kernel.E6O2.Checks
public import Certificates.Kernel.E6Syl3.Checks

public section

namespace CFSG.KD.E6O2

open CFSG.KC.E6O2

theorem e6O2Regular :
    CFSG.LieType.SeitzGeneration.ExcWideThree.E6O2Regular :=
  e6O2Regular_of_checks (g2 := g2) (g5 := g5) (gw := CFSG.KD.E6Syl3.gw) (w2 := w2) (w3 := w3)
    (w5 := w5) (by rw [ch214104_t2]; exact ch214104_s2) (by rw [ch214104_t5]; exact ch214104_s5)
    (by rw [CFSG.KD.E6Syl3.ch214105_tups]; exact CFSG.KD.E6Syl3.ch214105_q)
    (by rw [ch214104_t2]; exact ch214104_w2)
    (by rw [CFSG.KD.E6Syl3.ch214105_tups]; exact ch214104_w3)
    (by rw [ch214104_t5]; exact ch214104_w5)

end CFSG.KD.E6O2
