module

public import Certificates.Data.Kernel.G2Three.Q16
public import Certificates.Kernel.G2Three.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

theorem ch77002_k : q16K XS 64 = true := by quickRfl

end CFSG.KD.G2Three

end
