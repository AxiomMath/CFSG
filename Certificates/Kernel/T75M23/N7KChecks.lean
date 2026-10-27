module

public import Certificates.Data.Kernel.T75M23.N7K
public import Certificates.Kernel.CosPresTab.M23Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.KC.TabWord.M23 (NL)

theorem n7k_ok : n7kOk NL = true := by quickRfl

end CFSG.KC.N7K

end
