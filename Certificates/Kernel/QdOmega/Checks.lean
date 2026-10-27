module

public import Certificates.Data.Kernel.QdOmega
public import Certificates.Kernel.LocalQT.Syl.C4137
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataWords
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.QdOm

open CFSG.KC.QdOm CFSG.KD.LQT.C4137 CFSG.QuasithinUnique.Setup.X1
  CFSG.EvenSporadicStandard.M24Std

theorem ch24848e1 : enumK psiP psiIP plA plK = true := by quickRfl

theorem ch24848e2 : enumK psiP psiIP plB plK = true := by quickRfl

theorem ch24848cov : covK = true := by quickRfl

theorem ch24848om : omK GC m24RGens m24E1Bw wordQdOmega = true := by quickRfl

end CFSG.KD.QdOm

end
