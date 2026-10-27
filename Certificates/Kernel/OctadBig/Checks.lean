module

public import Certificates.Data.Kernel.OctadBig
public import Certificates.Kernel.LocalQT.Syl.C4137
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairB0

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.OctadBig

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.OctadBig CFSG.KD.LQT.C4137 CFSG.QuasithinUnique.Setup.X1
  CFSG.EvenSporadicStandard.M24Std

theorem ch24852 : obK GC m24RGens m24E1Bw m24B0Bw pairGenW
    [-1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1, -1, -1, -2, 1]
    [1, 2, 1, 2, 1, 2] [-1, 1, 1, -2, -1, 1, 1, -2] = true := by quickRfl

end CFSG.KD.OctadBig

end
