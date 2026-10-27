module

public import Certificates.Kernel.HN1408.Tr2Defs
public import Certificates.Kernel.HN1408.Cz1TData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cz1T

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.Tr2

theorem cz1T_head : headK classz₁.centGens wordZ₁ G T0 T1 = true := by quickRfl

theorem cz1T_keys : keysK 160 T0 = true := by quickRfl

theorem cz1T_tree : allN 160 (treeK 2 160 G T0 P0) = true := by quickRfl

theorem cz1T_sch : allN 2 (schK 2 160 G T0 S SR) = true := by quickRfl

theorem cz1T_t1 : allN 24 (t1K 2 S T1 P1) = true := by quickRfl

end CFSG.KD.HN1408.Cz1T

end
