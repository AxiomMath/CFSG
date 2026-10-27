module

public import Certificates.Kernel.HN1408.ClsGDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words
public import Certificates.Kernel.HN1408.SqZDefs

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26774cg rep CFSG.KD.HN1408.ClsR.gRep 0 14

public section

namespace CFSG.KD.HN1408.ClsR

theorem g_root : rootK SqZ.g1Word ClsG.R = true := by quickRfl

end CFSG.KD.HN1408.ClsR

end
