module

public import Certificates.Kernel.HN1408.Tr2Defs
public import Certificates.Kernel.HN1408.SqTData
public import Certificates.Kernel.HN1408.SqZDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SqT

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408.Tr2 CFSG.KD.HN1408.SqZ

theorem sqT_head : headK g1Cent g1Word G T0 T1 = true := by quickRfl

theorem sqT_keys : keysK 720 T0 = true := by quickRfl

theorem sqT_tree : allN 720 (treeK 3 720 G T0 P0) = true := by quickRfl

theorem sqT_sch : allN 3 (schK 3 720 G T0 S SR) = true := by quickRfl

theorem sqT_t1 : allN 8 (t1K 3 S T1 P1) = true := by quickRfl

end CFSG.KD.HN1408.SqT

end
