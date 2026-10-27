module

public import Certificates.Data.Kernel.G2Three.Gen
public import Certificates.Kernel.G2Three.K7bRec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

theorem g2Gen1208102_ok : g2GenK K7G = true := by quickRfl

end CFSG.KD.G2Three

end
