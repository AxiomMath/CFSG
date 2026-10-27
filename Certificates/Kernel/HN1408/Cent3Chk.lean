module

public import Certificates.Kernel.HN1408.Cent3Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open CFSG.KC.Enum CFSG.KS

theorem ch441603_head : headK G T0 T1 = true := by quickRfl

theorem ch441603_keys : keysK T0 = true := by quickRfl

theorem ch441603_tree : allN 40 (treeK G T0 P0) = true := by quickRfl

theorem ch441603_sch : allN 3 (schK G T0 S SR) = true := by quickRfl

theorem ch441603_t1 : allN 36 (t1K S T1 P1) = true := by quickRfl

theorem ch441603_rep : allN 6 (repK RK RT RW) = true := by quickRfl

theorem ch441603_x : xK X = true := by quickRfl

end CFSG.KD.HN1408.Cent3

end
