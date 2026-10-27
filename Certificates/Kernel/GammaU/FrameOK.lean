module

public import Certificates.Kernel.GammaU.FrameData
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs
public import Certificates.Data.Kernel.GammaUSigmaK
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUF cf16966sj CFSG.KD.GUF.sjOK 0 2

namespace CFSG.KD.GUF

open CFSG.KC.IF4C CFSG.KC.GUV

theorem cf16966_cg : cgOK = true := by decide +kernel

theorem cf16966_dt : dtsOK = true := by decide +kernel

theorem cf16966_te : teOK = true := by decide +kernel

theorem cf16966_sa : saOK = true := by decide +kernel

theorem cf16966_sap : SA = CFSG.GF2Type.Smith1979.GammaU.StepA.saGens.map CFSG.KC.IF4R.packR ∧
    (CFSG.GF2Type.Smith1979.GammaU.StepA.saGens.all fun r => CFSG.KC.GUS.rowsOK r.toList) = true := by
  decide +kernel

end CFSG.KD.GUF

end
