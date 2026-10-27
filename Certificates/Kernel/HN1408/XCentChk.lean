module

public import Certificates.Kernel.HN1408.XCentDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch441898 good CFSG.KD.HN1408.XCent.goodD 0 6
#kc_each CFSG.KD.HN1408.ch441898 scan CFSG.KD.HN1408.XCent.scanD 0 6
#kc_each CFSG.KD.HN1408.ch441898 cnt CFSG.KD.HN1408.XCent.cntD 0 6

public section

namespace CFSG.KD.HN1408.XCent

theorem head_ok : xcHead = true := by quickRfl

theorem words_ok : xcWords E = true := by quickRfl

theorem center_ok : xcCenter E = true := by quickRfl

theorem norm_ok : xcNorm E = true := by quickRfl

end CFSG.KD.HN1408.XCent

end
