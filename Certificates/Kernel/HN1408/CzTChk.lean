module

public import Certificates.Kernel.HN1408.CzTDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzT

open CFSG.KC.Enum CFSG.KS

theorem czT_head : headK G T0 T1 = true := by quickRfl

theorem czT_keys : keysK T0 = true := by quickRfl

theorem czT_sch : allN nS (schK G T0 S SR) = true := by quickRfl

theorem czT_t1 : allN n1 (t1K S T1 P1) = true := by quickRfl

end CFSG.KD.HN1408.CzT

end
