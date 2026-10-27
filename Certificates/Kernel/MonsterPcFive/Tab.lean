module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcFive.Model

public section

namespace CFSG.KC.MonPcFiveD

open CFSG.KC.MonPcFive

theorem tabT : tabOK () = true := by decide +kernel

theorem tauT : tauOK () = true := by decide +kernel

theorem sigT : sigOK () = true := by decide +kernel

end CFSG.KC.MonPcFiveD

end
