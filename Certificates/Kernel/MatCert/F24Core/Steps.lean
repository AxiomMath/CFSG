module

public import Certificates.Kernel.MatCert.F24Core.Vals
public import Certificates.Kernel.MatCert.F24Core.StepsK0
public import Certificates.Kernel.MatCert.F24Core.StepsK1
public import Certificates.Kernel.MatCert.F24Core.StepsK2
public import Certificates.Kernel.MatCert.F24Core.StepsK3
public import Certificates.Kernel.MatCert.F24Core.StepsK4
public import Certificates.Kernel.MatCert.F24Core.StepsK5
public import Certificates.Kernel.MatCert.F24Core.StepsK6
public import Certificates.Kernel.MatCert.F24Core.StepsK7
import Certificates.Kernel.LocalQT.CmdF3
import CFSG.Certificates.Kernel.LocalQT.StepsF3Sound
import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_chain3 CFSG.KD.MC.F24C 20

namespace CFSG.KD.MC.F24C

open CFSG.KC.LocalComp.Ops3Snd in
public theorem steps : CFSG.KC.LQT.StepsTo (CFSG.KC.LQT.stepOK lay V P) N :=
  CFSG.KC.LQT.F3S.steps_of_F3 lay_ok rfl (by decide) (by decide)
    (mat3_decode lay lay_ok rfl decA).1 (mat3_decode lay lay_ok rfl decB).1
    (by rw [one]; exact (mat3_one lay lay_ok rfl).1) steps3

end CFSG.KD.MC.F24C
