module

public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import Certificates.Kernel.ONanA6.Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.ONanA6

open CFSG.KC.LQT.S CFSG.QuasithinUnique.A6Facts

theorem hl : Core.pslLit.map codeL = lc := by decide +kernel

theorem hr : Core.autReps.map codeL = rc := by decide +kernel

theorem hg : Core.pslGenC.map codeL = gc := by decide +kernel

end CFSG.KD.ONanA6

end
