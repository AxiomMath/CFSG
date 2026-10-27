module

public import Certificates.Kernel.HN1408.Tab4CntDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs
public import Certificates.Kernel.HN1408.TabXCntDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbT

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.Tr2

theorem cbT_head : headK classb.centGens wordB G T0 T1 = true := by quickRfl

theorem cbT_keys : keysK 672 T0 = true := by quickRfl

theorem cbT_tree : allN 672 (treeK 2 672 G T0 P0) = true := by quickRfl

theorem cbT_sch : allN nS (schK 2 672 G T0 S SR) = true := by quickRfl

theorem cbT_t1 : allN 1 (t1K nS S T1 P1) = true := by quickRfl

theorem cbT_t1P : allN 120 (t1PK 1401 1 nS S T1 P1) = true := by quickRfl

end CFSG.KD.HN1408.CbT

end
