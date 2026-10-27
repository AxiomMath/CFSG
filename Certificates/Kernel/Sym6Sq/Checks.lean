module

public import Certificates.Data.Kernel.Sym6Sq
public import Certificates.Kernel.LocalQT.Syl.C4137
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.Sym6Sq

open CFSG.KC.Sym6Sq CFSG.KD.LQT.C4137 CFSG.QuasithinUnique.Setup.X1
  CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M24Std.Sym6

theorem ch25731bfs : bfsChk GC wordSxS wordSxT = true := by quickRfl

theorem ch25731om : normChk GC m24RGens m24E1Bw wordQdOmega = true := by quickRfl

theorem ch25731sq :
    sqChk GC m24RGens m24E1Bw wordSxS wordSxT wordQdOmega 16 8 = true := by quickRfl

end CFSG.KD.Sym6Sq

end
