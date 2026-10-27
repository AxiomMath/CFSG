
module

public import Certificates.Kernel.GammaU.Census0Data
public import Certificates.Kernel.GammaU.Census1Data
public import CFSG.Certificates.Kernel.IdxFourChainSound
public import CFSG.GF2Type.Smith1979.GammaU.StepCInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUSB

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem s0_mem_0 : rowsP CFSG.KD.GUC0.S0 ∈ unitaryElts 0 := by decide +kernel

theorem s0_mem_1 : rowsP CFSG.KD.GUC1.S0 ∈ unitaryElts 1 := by decide +kernel

end CFSG.KD.GUSB

end
