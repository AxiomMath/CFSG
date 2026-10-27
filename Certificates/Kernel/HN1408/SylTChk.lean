module

public import Certificates.Kernel.HN1408.SylTDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylT

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask CFSG.KD.HN1408
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem genIdx_ok : genIdxK = true := by quickRfl

theorem comm_ok : commK = true := by quickRfl

theorem sub1_ok : subK E1 PL1 C1 G1 6 128 = true := by quickRfl

theorem sub2_ok : subK E2 PL2 C2 G2 8 512 = true := by quickRfl

theorem g1_ok : g1K = true := by quickRfl

theorem g2_ok : g2K = true := by quickRfl

theorem norm_ok : normK = true := by quickRfl

theorem invW0_ok : invW0K = true := by quickRfl

theorem counts_ok : countsK = true := by quickRfl

theorem genBlk_ok : genBlkK = true := by quickRfl

theorem tg_ok : tgK = true := by quickRfl

theorem cent_ok : centK = true := by quickRfl

end CFSG.KD.HN1408.SylT

end
