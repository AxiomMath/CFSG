module

public import Certificates.Kernel.He589208.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He589208.CK

open CFSG.KC.DcK

theorem inv : K.invOK = true := by quickRfl
theorem basic : K.basicOK = true := by quickRfl
theorem lab : K.labOK = true := by quickRfl
theorem dist : K.distOK IV = true := by quickRfl
theorem edges : K.edgesOK = true := by quickRfl
theorem vs : K.vsOK = true := by quickRfl
theorem hit : K.hitOK HitV = true := by quickRfl
theorem mass : K.massOK HitV = true := by quickRfl

end CFSG.KD.He589208.CK

end
