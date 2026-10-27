module

public import Certificates.Data.Kernel.GammaUStepA.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUA

open CFSG.KC.IF4C CFSG.KC.GUA CFSG.GF2Type.Smith1979.GammaU.StepA

theorem cs16964_pin : pinOK = true := by quickRfl

theorem cs16964_t1r0 : t1OK (nthD [] dReps 0) W0 = true := by quickRfl

theorem cs16964_t1r2 : t1OK (nthD [] dReps 2) W2 = true := by quickRfl

theorem cs16964_t1r4 : t1OK (nthD [] dReps 4) W4 = true := by quickRfl

theorem cs16964_t1r5 : t1OK (nthD [] dReps 5) W5 = true := by quickRfl

theorem cs16964_bad3 : badOK (nthD [] dReps 3) = true := by quickRfl

theorem cs16964_theta : thetaOK = true := by quickRfl

theorem cs16964_b10 : b10OK = true := by quickRfl

theorem cs16964_coef : coefOK = true := by quickRfl

theorem cs16964_span : spanOK = true := by quickRfl

theorem cs16964_perp : perpOK = true := by quickRfl

theorem cs16964_ker : kerOK THP K0P = true := by quickRfl

theorem cs16964_gens : genTOK THP = true := by quickRfl

theorem cs16964_comm : commOK = true := by quickRfl

theorem cs16964_rho : rhoOK = true := by quickRfl

end CFSG.KD.GUA

end
