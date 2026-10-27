module

public import Certificates.Kernel.HN1408.AKDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.AK

theorem basic_ok : basicK = true := by quickRfl

theorem half_ok : halfK = true := by quickRfl

theorem genBlkP_ok : genBlkPK = true := by quickRfl

theorem cent_ok : centK = true := by quickRfl

theorem norm_ok : normK = true := by quickRfl

theorem fuse_ok : fuseK = true := by decide +kernel

theorem fuseRel_ok : fuseRelK = true := by quickRfl
end CFSG.KD.HN1408.AK

end
