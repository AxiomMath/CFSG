module

public import Certificates.Data.Kernel.T75M23.L2K7D
public import Certificates.Kernel.CosPresTab.M23Tab
public import Certificates.Kernel.T75M23.L2K7Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.KC.TabWord.M23 (NL)

theorem icK_ok : icK NL CFSG.KD.T75M23L2.ic = true := by quickRfl

end CFSG.KC.N7K

end
